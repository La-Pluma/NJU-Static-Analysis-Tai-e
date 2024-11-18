/*
 * Tai-e: A Static Analysis Framework for Java
 *
 * Copyright (C) 2022 Tian Tan <tiantan@nju.edu.cn>
 * Copyright (C) 2022 Yue Li <yueli@nju.edu.cn>
 *
 * This file is part of Tai-e.
 *
 * Tai-e is free software: you can redistribute it and/or modify
 * it under the terms of the GNU Lesser General Public License
 * as published by the Free Software Foundation, either version 3
 * of the License, or (at your option) any later version.
 *
 * Tai-e is distributed in the hope that it will be useful,but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY
 * or FITNESS FOR A PARTICULAR PURPOSE. See the GNU Lesser General
 * Public License for more details.
 *
 * You should have received a copy of the GNU Lesser General Public
 * License along with Tai-e. If not, see <https://www.gnu.org/licenses/>.
 */

package pascal.taie.analysis.graph.callgraph;

import pascal.taie.World;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JClass;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.classes.Subsignature;

import java.util.LinkedList;
import java.util.Set;
import java.util.Queue;

/**
 * Implementation of the CHA algorithm.
 */
class CHABuilder implements CGBuilder<Invoke, JMethod> {

    private ClassHierarchy hierarchy;

    @Override
    public CallGraph<Invoke, JMethod> build() {
        hierarchy = World.get().getClassHierarchy();
        return buildCallGraph(World.get().getMainMethod());
    }

    private CallGraph<Invoke, JMethod> buildCallGraph(JMethod entry) {
        DefaultCallGraph callGraph = new DefaultCallGraph();
        callGraph.addEntryMethod(entry);
        // TODO - finish me
        Queue<JMethod> workList = new LinkedList<>();
        workList.add(entry);
        while (!workList.isEmpty()) {
            JMethod caller = workList.poll();
            if (callGraph.addReachableMethod(caller)){
                for (Invoke callSite : callGraph.getCallSitesIn(caller)) {
                    Set<JMethod> targets = resolve(callSite);
                    for (JMethod target : targets) {
                        CallKind kind = CallGraphs.getCallKind(callSite);
                        callGraph.addEdge(new Edge<>(kind, callSite, target));
                        workList.add(target);
                    }
                }
            }
        }
        return callGraph;
    }

    /**
     * Resolves call targets (callees) of a call site via CHA.
     */
    private Set<JMethod> resolve(Invoke callSite) {
        // TODO - finish me
        assert callSite != null; // callSite should not be null
        Set<JMethod> targetsMethod = new java.util.HashSet<>();
        MethodRef csRef = callSite.getMethodRef();
        JClass csDeclaringClass = csRef.getDeclaringClass();
        Subsignature csSubsignature = csRef.getSubsignature();

        switch (CallGraphs.getCallKind(callSite)) {
            case STATIC, SPECIAL -> {
                JMethod target = dispatch(csDeclaringClass, csSubsignature);
                if (target != null) {
                    targetsMethod.add(target);
                }
            }
            case VIRTUAL, INTERFACE -> {
                Queue<JClass> workList = new LinkedList<>();
                workList.add(csDeclaringClass);
                while (!workList.isEmpty()) {
                    JClass jclass = workList.poll();
                    JMethod target = dispatch(jclass, csSubsignature);
                    if (target != null) {
                        targetsMethod.add(target);
                    }
                    if (jclass.isInterface()) {
                        workList.addAll(hierarchy.getDirectImplementorsOf(jclass));
                        workList.addAll(hierarchy.getDirectSubinterfacesOf(jclass));
                    } else {
                        workList.addAll(hierarchy.getDirectSubclassesOf(jclass));
                    }
                }
            }
            default -> {
            }
            //do nothing, we do not need to handle dynamic calls and other calls
        }
        return targetsMethod;
    }

    /**
     * Looks up the target method based on given class and method subsignature.
     *
     * @return the dispatched target method, or null if no satisfying method
     * can be found.
     */
    private JMethod dispatch(JClass jclass, Subsignature subsignature) {
        // TODO - finish me
        assert subsignature != null; // subSignature should not be null
        if(jclass == null){
            return null;
        }
        JMethod target = jclass.getDeclaredMethod(subsignature);
        if (target != null) {
            // If the target method is abstract, it cannot be instantiated.
            if (target.isAbstract()) {
                return null;
            }
            return target;
        }
        return dispatch(jclass.getSuperClass(), subsignature);
    }
}

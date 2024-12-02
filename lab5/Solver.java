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

package pascal.taie.analysis.pta.ci;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.DefaultCallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InvokeExp;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.proginfo.MethodRef;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.ClassHierarchy;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.AnalysisException;
import pascal.taie.language.type.Type;

import java.util.List;

class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final HeapModel heapModel;

    private DefaultCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private StmtProcessor stmtProcessor;

    private ClassHierarchy hierarchy;

    Solver(HeapModel heapModel) {
        this.heapModel = heapModel;
    }

    /**
     * Runs pointer analysis algorithm.
     */
    void solve() {
        initialize();
        analyze();
    }

    /**
     * Initializes pointer analysis.
     */
    private void initialize() {
        workList = new WorkList();
        pointerFlowGraph = new PointerFlowGraph();
        callGraph = new DefaultCallGraph();
        stmtProcessor = new StmtProcessor();
        hierarchy = World.get().getClassHierarchy();
        // initialize main method
        JMethod main = World.get().getMainMethod();
        callGraph.addEntryMethod(main);
        addReachable(main);
    }

    /**
     * Processes new reachable method.
     */
    private void addReachable(JMethod method) {
        // TODO - finish me
        if (callGraph.addReachableMethod(method)){
            for(Stmt stmt : method.getIR().getStmts()){
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes statements in new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {
        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            // x = new T
            Var var = stmt.getLValue();
            Pointer varPointer = pointerFlowGraph.getVarPtr(var);
            PointsToSet set = new PointsToSet(heapModel.getObj(stmt));
            workList.addEntry(varPointer, set);
            return null;
        }
        @Override
        public Void visit(Copy stmt) {
            // x = y
            Var lValue = stmt.getLValue();
            Var rValue= stmt.getRValue();
            Pointer lPointer = pointerFlowGraph.getVarPtr(lValue);
            Pointer rPointer = pointerFlowGraph.getVarPtr(rValue);
            addPFGEdge(rPointer, lPointer);
            return null;
        }
        @Override
        public Void visit(StoreField stmt) {
            // x.f = y
            if (stmt.isStatic()){
                Pointer fieldPointer = pointerFlowGraph.getStaticField(stmt.getFieldAccess().getFieldRef().resolve());
                Pointer varPointer = pointerFlowGraph.getVarPtr(stmt.getRValue());
                addPFGEdge(varPointer, fieldPointer);
            }
            return null;
        }
        @Override
        public Void visit(LoadField stmt) {
            // y = x.f
            if (stmt.isStatic()){
                Pointer varPointer = pointerFlowGraph.getVarPtr(stmt.getLValue());
                Pointer fieldPointer = pointerFlowGraph.getStaticField(stmt.getFieldAccess().getFieldRef().resolve());
                addPFGEdge(fieldPointer, varPointer);
            }
            return null;
        }
        @Override
        public Void visit(Invoke stmt) {
            // x.m(...)
            if (stmt.isStatic()){
                JMethod method = resolveCallee(null, stmt);
                if(callGraph.addEdge(new Edge<>(CallKind.STATIC, stmt, method))){
                    addReachable(method);
                    for (int i = 0; i < method.getParamCount(); i++){
                        Pointer argPointer = pointerFlowGraph.getVarPtr(stmt.getInvokeExp().getArg(i));
                        Pointer paramPointer = pointerFlowGraph.getVarPtr(method.getIR().getParam(i));
                        addPFGEdge(argPointer, paramPointer);
                    }
                    if (stmt.getResult() != null){
                        for (Var ret : method.getIR().getReturnVars()){
                            Pointer retPointer = pointerFlowGraph.getVarPtr(ret);
                            Pointer resultPointer = pointerFlowGraph.getVarPtr(stmt.getResult());
                            addPFGEdge(retPointer, resultPointer);
                        }
                    }
                }
            }
            return null;
        }
    }

    /**
     * Adds an edge "source -> target" to the PFG.
     */
    private void addPFGEdge(Pointer source, Pointer target) {
        // TODO - finish me
        if(pointerFlowGraph.addEdge(source, target)){
            PointsToSet sourcePts = source.getPointsToSet();
            if(!sourcePts.isEmpty()){
                workList.addEntry(target, sourcePts);
            }
        }
    }

    /**
     * Processes work-list entries until the work-list is empty.
     */
    private void analyze() {
        // TODO - finish me
        while(!workList.isEmpty()){
            WorkList.Entry entry = workList.pollEntry();
            Pointer pointer = entry.pointer();
            PointsToSet pointsToSet = entry.pointsToSet();
            // delta = pts - pt(n)
            PointsToSet delta = propagate(pointer, pointsToSet);

            if (pointer instanceof VarPtr varPtr) {
                Var var = varPtr.getVar();
                for (Obj obj : delta) {
                    for (StoreField storeField : var.getStoreFields()){
                        //x.f = y
                        Pointer fieldPointer = pointerFlowGraph.getInstanceField(obj, storeField.getFieldRef().resolve());
                        Pointer varPointer = pointerFlowGraph.getVarPtr(storeField.getRValue());
                        addPFGEdge(varPointer, fieldPointer);
                    }
                    for (LoadField loadField : var.getLoadFields()){
                        //y = x.f
                        Pointer varPointer = pointerFlowGraph.getVarPtr(loadField.getLValue());
                        Pointer fieldPointer = pointerFlowGraph.getInstanceField(obj, loadField.getFieldRef().resolve());
                        addPFGEdge(fieldPointer, varPointer);
                    }
                    for (StoreArray storeArray : var.getStoreArrays()){
                        //x[i] = y
                        Pointer arrayPointer = pointerFlowGraph.getArrayIndex(obj);
                        Pointer varPointer = pointerFlowGraph.getVarPtr(storeArray.getRValue());
                        addPFGEdge(varPointer, arrayPointer);
                    }
                    for (LoadArray loadArray : var.getLoadArrays()){
                        //y = x[i]
                        Pointer varPointer = pointerFlowGraph.getVarPtr(loadArray.getLValue());
                        Pointer arrayPointer = pointerFlowGraph.getArrayIndex(obj);
                        addPFGEdge(arrayPointer, varPointer);
                    }
                    processCall(var, obj);
                }
            }
        }
    }

    /**
     * Propagates pointsToSet to pt(pointer) and its PFG successors,
     * returns the difference set of pointsToSet and pt(pointer).
     */
    private PointsToSet propagate(Pointer pointer, PointsToSet pointsToSet) {
        // TODO - finish me
        PointsToSet deltaPts = new PointsToSet();
        PointsToSet pointerPts = pointer.getPointsToSet();
        for(Obj obj : pointsToSet){
            if(!pointerPts.contains(obj)){
                deltaPts.addObject(obj);
            }
        }

        if (!deltaPts.isEmpty()){
            for(Obj obj : deltaPts){
                pointerPts.addObject(obj);
                for(Pointer succ : pointerFlowGraph.getSuccsOf(pointer)){
                    workList.addEntry(succ, deltaPts);
                }
            }
        }

        return deltaPts;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param var the variable that holds receiver objects
     * @param recv a new discovered object pointed by the variable.
     */
    private void processCall(Var var, Obj recv) {
        // TODO - finish me
        for(Invoke invoke : var.getInvokes()){
            JMethod method = resolveCallee(recv, invoke);
            IR methodIR = method.getIR();
            Var thisVar = methodIR.getThis();
            if(thisVar != null) {
                //means is not static
                Pointer thisPointer = pointerFlowGraph.getVarPtr(thisVar);
                workList.addEntry(thisPointer, new PointsToSet(recv));
                if(callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), invoke, method))){
                    addReachable(method);
                    for(int i = 0; i < method.getParamCount(); i++){
                        Pointer argPointer = pointerFlowGraph.getVarPtr(invoke.getInvokeExp().getArg(i));
                        Pointer paramPointer = pointerFlowGraph.getVarPtr(methodIR.getParam(i));
                        addPFGEdge(argPointer, paramPointer);
                    }
                    if(invoke.getResult() != null){
                        // invoke stmt have result, y exists
                        // y = x.m(...)
                        for(Var ret : methodIR.getReturnVars()){
                            Pointer retPointer = pointerFlowGraph.getVarPtr(ret);
                            Pointer resultPointer = pointerFlowGraph.getVarPtr(invoke.getResult());
                            addPFGEdge(retPointer, resultPointer);
                        }
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv     the receiver object of the method call. If the callSite
     *                 is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(Obj recv, Invoke callSite) {
        Type type = recv != null ? recv.getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    CIPTAResult getResult() {
        return new CIPTAResult(pointerFlowGraph, callGraph);
    }
}

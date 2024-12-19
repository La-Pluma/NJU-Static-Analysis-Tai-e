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

package pascal.taie.analysis.pta.cs;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraphs;
import pascal.taie.analysis.graph.callgraph.CallKind;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.PointerAnalysisResultImpl;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.ArrayIndex;
import pascal.taie.analysis.pta.core.cs.element.CSCallSite;
import pascal.taie.analysis.pta.core.cs.element.CSManager;
import pascal.taie.analysis.pta.core.cs.element.CSMethod;
import pascal.taie.analysis.pta.core.cs.element.CSObj;
import pascal.taie.analysis.pta.core.cs.element.CSVar;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.cs.element.MapBasedCSManager;
import pascal.taie.analysis.pta.core.cs.element.Pointer;
import pascal.taie.analysis.pta.core.cs.element.StaticField;
import pascal.taie.analysis.pta.core.cs.selector.ContextSelector;
import pascal.taie.analysis.pta.core.heap.HeapModel;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.plugin.taint.TaintAnalysiss;
import pascal.taie.analysis.pta.pts.PointsToSet;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.config.AnalysisOptions;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;

public class Solver {

    private static final Logger logger = LogManager.getLogger(Solver.class);

    private final AnalysisOptions options;

    private final HeapModel heapModel;

    private final ContextSelector contextSelector;

    private CSManager csManager;

    private CSCallGraph callGraph;

    private PointerFlowGraph pointerFlowGraph;

    private WorkList workList;

    private TaintAnalysiss taintAnalysis;

    private PointerAnalysisResult result;

    Solver(AnalysisOptions options, HeapModel heapModel,
           ContextSelector contextSelector) {
        this.options = options;
        this.heapModel = heapModel;
        this.contextSelector = contextSelector;
    }

    public AnalysisOptions getOptions() {
        return options;
    }

    public ContextSelector getContextSelector() {
        return contextSelector;
    }

    public CSManager getCSManager() {
        return csManager;
    }

    public void workListAddEntry(Pointer pointer, PointsToSet pointsToSet) {
        // TaintAnalysis can not directly call workList.addEntry()
        workList.addEntry(pointer, pointsToSet);
    }

    void solve() {
        initialize();
        analyze();
        taintAnalysis.onFinish();
    }

    private void initialize() {
        csManager = new MapBasedCSManager();
        callGraph = new CSCallGraph(csManager);
        pointerFlowGraph = new PointerFlowGraph();
        workList = new WorkList();
        taintAnalysis = new TaintAnalysiss(this);
        // process program entry, i.e., main method
        Context defContext = contextSelector.getEmptyContext();
        JMethod main = World.get().getMainMethod();
        CSMethod csMethod = csManager.getCSMethod(defContext, main);
        callGraph.addEntryMethod(csMethod);
        addReachable(csMethod);
    }

    /**
     * Processes new reachable context-sensitive method.
     */
    private void addReachable(CSMethod csMethod) {
        // TODO - finish me
        StmtProcessor stmtProcessor = new StmtProcessor(csMethod);
        if(callGraph.addReachableMethod(csMethod)){
            for(Stmt stmt : csMethod.getMethod().getIR().getStmts()){
                stmt.accept(stmtProcessor);
            }
        }
    }

    /**
     * Processes the statements in context-sensitive new reachable methods.
     */
    private class StmtProcessor implements StmtVisitor<Void> {

        private final CSMethod csMethod;

        private final Context context;

        private StmtProcessor(CSMethod csMethod) {
            this.csMethod = csMethod;
            this.context = csMethod.getContext();
        }

        // TODO - if you choose to implement addReachable()
        //  via visitor pattern, then finish me
        @Override
        public Void visit(New stmt) {
            // x = new T
            CSVar varPtr = csManager.getCSVar(context, stmt.getLValue());
            Obj obj = heapModel.getObj(stmt);
            Context objContext = contextSelector.selectHeapContext(csMethod, obj);
            CSObj csObj = csManager.getCSObj(objContext, obj);
            workList.addEntry(varPtr, PointsToSetFactory.make(csObj));
            return null;
        }
        @Override
        public Void visit(Copy stmt){
            // x = y
            CSVar leftPtr = csManager.getCSVar(context, stmt.getLValue());
            CSVar rightPtr = csManager.getCSVar(context, stmt.getRValue());
            addPFGEdge(rightPtr, leftPtr);
            return null;
        }
        @Override
        public Void visit(StoreField stmt){
            if(stmt.isStatic()){
                // T.f = x
                JField field = stmt.getFieldRef().resolve();
                StaticField fieldPtr = csManager.getStaticField(field);
                CSVar varPtr = csManager.getCSVar(context, stmt.getRValue());
                addPFGEdge(varPtr, fieldPtr);
            }
            return null;
        }
        @Override
        public Void visit(LoadField stmt){
            if(stmt.isStatic()){
                // x = T.f
                CSVar varPtr = csManager.getCSVar(context, stmt.getLValue());
                JField field = stmt.getFieldRef().resolve();
                StaticField fieldPtr = csManager.getStaticField(field);
                addPFGEdge(fieldPtr, varPtr);
            }
            return null;
        }
        @Override
        public Void visit(Invoke stmt) {
            if (stmt.isStatic()) {
                // l : r = T.m(a1, ..., an)
                JMethod callee = resolveCallee(null, stmt);
                CSCallSite csInvoke = csManager.getCSCallSite(context, stmt);
                Context ctContext = contextSelector.selectContext(csInvoke, callee);
                CSMethod csCallee = csManager.getCSMethod(ctContext, callee);

                taintAnalysis.taintTransferFlow(stmt, ctContext, context);
                if (callGraph.addEdge(new Edge<>(CallKind.STATIC, csInvoke, csCallee))) {
                    addReachable(csCallee);
                    for (int i = 0; i < callee.getParamCount(); i++) {
                        CSVar argPtr = csManager.getCSVar(context, stmt.getInvokeExp().getArg(i));
                        CSVar paramPtr = csManager.getCSVar(ctContext, callee.getIR().getParam(i));
                        addPFGEdge(argPtr, paramPtr);
                    }
                    if (stmt.getResult() != null) {
                        CSVar resultPtr = csManager.getCSVar(context, stmt.getResult());
                        taintAnalysis.taintSourceFlow(stmt, ctContext, resultPtr);
                        for (Var returnVar : callee.getIR().getReturnVars()) {
                            CSVar returnPtr = csManager.getCSVar(ctContext, returnVar);
                            addPFGEdge(returnPtr, resultPtr);
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
        if (pointerFlowGraph.addEdge(source, target)){
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

            PointsToSet delta = propagate(pointer, pointsToSet);
            if (pointer instanceof CSVar csVar){
                Var var = csVar.getVar();
                Context context = csVar.getContext();
                for(CSObj csObj : delta.getObjects()){
                    for(StoreField storeField : var.getStoreFields()){
                        // x.f = y
                        if(!storeField.isStatic()){
                            InstanceField fieldPtr = csManager.getInstanceField(csObj, storeField.getFieldRef().resolve());
                            CSVar varPtr = csManager.getCSVar(context, storeField.getRValue());
                            addPFGEdge(varPtr, fieldPtr);
                        }
                    }
                    for(LoadField loadField : var.getLoadFields()){
                        // y = x.f
                        if(!loadField.isStatic()){
                            CSVar varPtr = csManager.getCSVar(context, loadField.getLValue());
                            InstanceField fieldPtr = csManager.getInstanceField(csObj, loadField.getFieldRef().resolve());
                            addPFGEdge(fieldPtr, varPtr);
                        }
                    }
                    for(StoreArray storeArray : var.getStoreArrays()){
                        // x[i] = y
                        ArrayIndex arrayPtr = csManager.getArrayIndex(csObj);
                        CSVar varPtr = csManager.getCSVar(context, storeArray.getRValue());
                        addPFGEdge(varPtr, arrayPtr);
                    }
                    for(LoadArray loadArray : var.getLoadArrays()){
                        // y = x[i]
                        ArrayIndex arrayPtr = csManager.getArrayIndex(csObj);
                        CSVar varPtr = csManager.getCSVar(context, loadArray.getLValue());
                        addPFGEdge(arrayPtr, varPtr);
                    }

                    taintAnalysis.taintBroadcast(callGraph, csObj.getObject(), var);
                    processCall(csVar, csObj);
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
        PointsToSet delta = PointsToSetFactory.make();
        PointsToSet pointerPts = pointer.getPointsToSet();
        for(CSObj obj : pointsToSet.getObjects()){
            if(!pointerPts.contains(obj)){
                delta.addObject(obj);
            }
        }

        if(!delta.isEmpty()){
            pointerPts.addAll(delta);
            for(Pointer succ : pointerFlowGraph.getSuccsOf(pointer)) {
                workList.addEntry(succ, delta);
            }
        }

        return delta;
    }

    /**
     * Processes instance calls when points-to set of the receiver variable changes.
     *
     * @param recv    the receiver variable
     * @param recvObj set of new discovered objects pointed by the variable.
     */
    private void processCall(CSVar recv, CSObj recvObj) {
        // TODO - finish me
        Var var = recv.getVar();
        for (Invoke invoke : var.getInvokes()){
            if(!invoke.isStatic()) {
                JMethod callee = resolveCallee(recvObj, invoke);
                CSCallSite csInvoke = csManager.getCSCallSite(recv.getContext(), invoke);
                Context context = contextSelector.selectContext(csInvoke, recvObj, callee);
                CSMethod csCallee = csManager.getCSMethod(context, callee);
                Var thisVar = callee.getIR().getThis();
                CSVar thisCSVar = csManager.getCSVar(context, thisVar);
                workList.addEntry(thisCSVar, PointsToSetFactory.make(recvObj));

                taintAnalysis.taintTransferFlow(invoke, context, recv.getContext());
                if (callGraph.addEdge(new Edge<>(CallGraphs.getCallKind(invoke), csInvoke, csCallee))){
                    addReachable(csCallee);

                    for(int i = 0; i < callee.getParamCount(); i++){
                        CSVar argPtr = csManager.getCSVar(recv.getContext(), invoke.getInvokeExp().getArg(i));
                        CSVar paramPtr = csManager.getCSVar(context, callee.getIR().getParam(i));
                        addPFGEdge(argPtr, paramPtr);
                    }

                    if(invoke.getResult() != null){
                        Var resultVar = invoke.getResult();
                        CSVar resultPtr = csManager.getCSVar(recv.getContext(), resultVar);
                        taintAnalysis.taintSourceFlow(invoke, context, resultPtr);
                        for(Var returnVar : callee.getIR().getReturnVars()){
                            CSVar returnPtr = csManager.getCSVar(context, returnVar);
                            // Why remove it form loop may cause failure?
                            //CSVar resultPtr = csManager.getCSVar(recv.getContext(), resultVar);
                            addPFGEdge(returnPtr, resultPtr);
                        }
                    }
                }
            }
        }
    }

    /**
     * Resolves the callee of a call site with the receiver object.
     *
     * @param recv the receiver object of the method call. If the callSite
     *             is static, this parameter is ignored (i.e., can be null).
     * @param callSite the call site to be resolved.
     * @return the resolved callee.
     */
    private JMethod resolveCallee(CSObj recv, Invoke callSite) {
        Type type = recv != null ? recv.getObject().getType() : null;
        return CallGraphs.resolveCallee(type, callSite);
    }

    public PointerAnalysisResult getResult() {
        if (result == null) {
            result = new PointerAnalysisResultImpl(csManager, callGraph);
        }
        return result;
    }
}



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

package pascal.taie.analysis.pta.plugin.taint;

import org.apache.logging.log4j.LogManager;
import org.apache.logging.log4j.Logger;
import pascal.taie.World;
import pascal.taie.analysis.graph.callgraph.CallGraph;
import pascal.taie.analysis.graph.callgraph.Edge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.CSCallGraph;
import pascal.taie.analysis.pta.core.cs.context.Context;
import pascal.taie.analysis.pta.core.cs.element.*;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.analysis.pta.cs.Solver;
import pascal.taie.analysis.pta.pts.PointsToSetFactory;
import pascal.taie.ir.exp.InvokeInstanceExp;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.Invoke;
import pascal.taie.language.classes.JMethod;
import pascal.taie.language.type.Type;
import soot.jimple.InstanceInvokeExpr;

import java.util.Set;
import java.util.TreeSet;

public class TaintAnalysiss {

    private static final Logger logger = LogManager.getLogger(TaintAnalysiss.class);

    private final TaintManager manager;

    private final TaintConfig config;

    private final Solver solver;

    private final CSManager csManager;

    private final Context emptyContext;

    public TaintAnalysiss(Solver solver) {
        manager = new TaintManager();
        this.solver = solver;
        csManager = solver.getCSManager();
        emptyContext = solver.getContextSelector().getEmptyContext();
        config = TaintConfig.readConfig(
                solver.getOptions().getString("taint-config"),
                World.get().getClassHierarchy(),
                World.get().getTypeSystem());
        logger.info(config);
    }

    // TODO - finish me

    public void onFinish() {
        Set<TaintFlow> taintFlows = collectTaintFlows();
        solver.getResult().storeResult(getClass().getName(), taintFlows);
    }

    private Set<TaintFlow> collectTaintFlows() {
        Set<TaintFlow> taintFlows = new TreeSet<>();
        PointerAnalysisResult result = solver.getResult();
        // TODO - finish me
        // You could query pointer analysis results you need via variable result.

        // sinkFlow
        for (Edge<CSCallSite, CSMethod> edge : result.getCSCallGraph().edges().toList()){
            CSCallSite csCallSite = edge.getCallSite();
            Invoke callSite = csCallSite.getCallSite();
            Context context = csCallSite.getContext();

            JMethod method = edge.getCallee().getMethod();

            for(int i = 0; i < callSite.getInvokeExp().getArgCount(); i++){
                Sink s = new Sink(method, i);
                if(config.getSinks().contains(s)){
                    Var arg = callSite.getInvokeExp().getArg(i);
                    CSVar csArg = csManager.getCSVar(context, arg);

                    for(CSObj csObj : result.getPointsToSet(csArg)){
                        Obj obj = csObj.getObject();
                        if(manager.isTaint(obj)){
                            Invoke source = manager.getSourceCall(obj);
                            TaintFlow taintFlow = new TaintFlow(source, callSite, i);
                            taintFlows.add(taintFlow);
                        }
                    }
                }
            }
        }

        return taintFlows;
    }

    public void taintSourceFlow(Invoke invoke, Context ctContext, CSVar csResultVar) {
        // handle taint source flow
        // should only be called when result exists
        JMethod method = invoke.getMethodRef().resolve();
        Type type = invoke.getMethodRef().getReturnType();
        Source s = new Source(method, type);
        if(config.getSources().contains(s)) {
            Obj taintObj = manager.makeTaint(invoke, type);
            CSObj csTaintObj = csManager.getCSObj(emptyContext, taintObj);

            solver.workListAddEntry(csResultVar, PointsToSetFactory.make(csTaintObj));
        }
    }

    public void taintTransferFlow(Invoke invoke, Context ctContext, Context context){

        for (TaintTransfer transfer : config.getTransfers()) {
            JMethod taintMethod = transfer.method();
            JMethod method = invoke.getMethodRef().resolve();
            if (method.equals(taintMethod)) {
                int from = transfer.from();
                int to = transfer.to();

                if(!invoke.isStatic()){
                    Var base = ((InvokeInstanceExp)(invoke.getInvokeExp())).getBase();
                    CSVar csBase = csManager.getCSVar(context, base);

                    if(invoke.getResult() != null){
                        Var resultVar = invoke.getResult();
                        CSVar csResultVar = csManager.getCSVar(context, resultVar);

                        if(from == TaintTransfer.BASE && to == TaintTransfer.RESULT){
                            // Base to Result
                            if (transfer.type().equals(invoke.getMethodRef().getReturnType())) {
                                for(CSObj csObj: solver.getResult().getPointsToSet(csBase)){
                                    Obj obj = csObj.getObject();
                                    if(manager.isTaint(obj)){
                                        Obj taintObj = manager.makeTaint(manager.getSourceCall(obj), resultVar.getType());
                                        CSObj csTaintObj = csManager.getCSObj(emptyContext, taintObj);
                                        solver.workListAddEntry(csResultVar, PointsToSetFactory.make(csTaintObj));
                                    }
                                }
                            }
                        }
                    }

                    if(from >= 0 && to == TaintTransfer.BASE){
                        // Arg to Base
                        if (transfer.type().equals(base.getType())) {
                            if(from < invoke.getInvokeExp().getArgCount()){
                                Var arg = invoke.getInvokeExp().getArg(from);
                                CSVar csArg = csManager.getCSVar(context, arg);

                                for (CSObj csObj : solver.getResult().getPointsToSet(csArg)) {
                                    Obj obj = csObj.getObject();
                                    if(manager.isTaint(obj)){
                                        Obj taintObj = manager.makeTaint(manager.getSourceCall(obj), base.getType());
                                        CSObj csTaintObj = csManager.getCSObj(emptyContext, taintObj);
                                        solver.workListAddEntry(csBase, PointsToSetFactory.make(csTaintObj));
                                    }
                                }
                            }
                        }
                    }
                }

                if(invoke.getResult() != null){
                    Var resultVar = invoke.getResult();
                    CSVar csResultVar = csManager.getCSVar(context, resultVar);

                    if(from >= 0 && to == TaintTransfer.RESULT){
                        // Arg to Result
                        if (transfer.type().equals(resultVar.getType())) {
                            if(from < invoke.getInvokeExp().getArgCount()){
                                Var arg = invoke.getInvokeExp().getArg(from);
                                CSVar csArg = csManager.getCSVar(context, arg);

                                for (CSObj csObj : solver.getResult().getPointsToSet(csArg)) {
                                    Obj obj = csObj.getObject();
                                    if(manager.isTaint(obj)){
                                        Obj taintObj = manager.makeTaint(manager.getSourceCall(obj), resultVar.getType());
                                        CSObj csTaintObj = csManager.getCSObj(emptyContext, taintObj);
                                        solver.workListAddEntry(csResultVar, PointsToSetFactory.make(csTaintObj));
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    public void taintBroadcast(CallGraph<CSCallSite, CSMethod> callGraph, Obj obj, Var var){
        if(manager.isTaint(obj)){
            for (Edge<CSCallSite, CSMethod> edge : callGraph.edges().toList()){
                Invoke callSite = edge.getCallSite().getCallSite();
                if(callSite.getInvokeExp().getArgs().contains(var)){
                    this.taintTransferFlow(callSite, edge.getCallee().getContext(), edge.getCallSite().getContext());
                }
            }
        }
    }
}

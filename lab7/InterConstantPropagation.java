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

package pascal.taie.analysis.dataflow.inter;

import pascal.taie.World;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.icfg.CallEdge;
import pascal.taie.analysis.graph.icfg.CallToReturnEdge;
import pascal.taie.analysis.graph.icfg.NormalEdge;
import pascal.taie.analysis.graph.icfg.ReturnEdge;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.cs.element.InstanceField;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.InstanceFieldAccess;
import pascal.taie.ir.exp.LValue;
import pascal.taie.ir.exp.RValue;
import pascal.taie.ir.exp.Var;
import pascal.taie.ir.stmt.*;
import pascal.taie.language.classes.JField;
import pascal.taie.language.classes.JMethod;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

import java.lang.reflect.Field;
import java.util.List;
import java.util.Map;

/**
 * Implementation of interprocedural constant propagation for int values.
 */
public class InterConstantPropagation extends
        AbstractInterDataflowAnalysis<JMethod, Stmt, CPFact> {

    public static final String ID = "inter-constprop";

    private final ConstantPropagation cp;

    private PointerAnalysisResult pta;

    private final MultiMap<Var, Var> aliasMap = Maps.newMultiMap();

    public InterConstantPropagation(AnalysisConfig config) {
        super(config);
        cp = new ConstantPropagation(new AnalysisConfig(ConstantPropagation.ID));
    }

    @Override
    protected void initialize() {
        String ptaId = getOptions().getString("pta");
        PointerAnalysisResult pta = World.get().getResult(ptaId);
        // You can do initialization work here
        this.pta = pta;
        calculateAlias(pta);
    }

    private void calculateAlias(PointerAnalysisResult pta) {
        MultiMap<Obj, Var> objToVar = Maps.newMultiMap();

        for(Var var : pta.getVars()){
            for(Obj obj : pta.getPointsToSet(var)){
                objToVar.put(obj, var);
            }
        }

        objToVar.forEachSet((obj, vars) -> {
            for(Var var : vars){
                // we add <var, var> to aliasMap too
                // alias relation is reflexive
                this.aliasMap.putAll(var, vars);
            }
        });
    }

    @Override
    public boolean isForward() {
        return cp.isForward();
    }

    @Override
    public CPFact newBoundaryFact(Stmt boundary) {
        IR ir = icfg.getContainingMethodOf(boundary).getIR();
        return cp.newBoundaryFact(ir.getResult(CFGBuilder.ID));
    }

    @Override
    public CPFact newInitialFact() {
        return cp.newInitialFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        cp.meetInto(fact, target);
    }

    @Override
    protected boolean transferCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        return out.copyFrom(in);
    }

    private class StmtProcessor implements StmtVisitor<Boolean> {
        private final CPFact in;
        private final CPFact out;

        private boolean isArrayAlias(Value index1, Value index2) {
            if(index1.isUndef() || index2.isUndef()){
                return false;
            }
            if(index1.isNAC() || index2.isNAC()){
                return true;
            }
            return index1.getConstant() == index2.getConstant();
        }

        public StmtProcessor(CPFact in, CPFact out) {
            this.in = in;
            this.out = out;
        }
        @Override
        public Boolean visitDefault(Stmt stmt) {
            return cp.transferNode(stmt, in, out);
        }
        @Override
        public Boolean visit(LoadField loadField) {
            // y = x.f
            CPFact origin = out.copy();
            out.copyFrom(in);

            Var left = loadField.getLValue();
            JField field = loadField.getFieldRef().resolve();

            if(ConstantPropagation.canHoldInt(left)){
                Value value = in.get(left);
                if(loadField.isStatic()){
                    for(Stmt stmt : icfg.getNodes()){
                        if(stmt instanceof StoreField storeField && storeField.isStatic()){
                            if(field.equals(storeField.getFieldRef().resolve())){
                                Var right = storeField.getRValue();
                                Value rightValue = solver.getResult().getInFact(storeField).get(right);
                                value = cp.meetValue(value, rightValue);
                            }
                        }
                    }
                }
                else if (loadField.getFieldAccess() instanceof InstanceFieldAccess access){
//                    System.out.println("-----------");
//                    System.out.println("load: " + loadField);
                    Var fieldBase = access.getBase();
                    for(Var alias : aliasMap.get(fieldBase)){
                        for (StoreField storeField : alias.getStoreFields()){
//                            System.out.println("store: " + storeField);
//                            System.out.println("loadField:" + field + " | " + "storeField:" + storeField.getFieldRef().resolve());
                            //why need check this?
                            if (field.equals(storeField.getFieldRef().resolve())) {
                                Var right = storeField.getRValue();
                                Value rightValue = solver.getResult().getInFact(storeField).get(right);
                                value = cp.meetValue(value, rightValue);
                            }
                        }
                    }
                }
                out.update(left, value);

                for(Stmt succ : icfg.getSuccsOf(loadField)) {
                    solver.getWorkList().add(succ);
                }
            }
            return !origin.equals(out);
        }
        @Override
        public Boolean visit(StoreField storeField) {
            // x.f = y
            CPFact origin = out.copy();
            out.copyFrom(in);

            Var right = storeField.getRValue();
            JField field = storeField.getFieldRef().resolve();
            // check y value change to broadcast
            if (ConstantPropagation.canHoldInt(right) && !origin.equals(out)){
                if (storeField.isStatic()) {
                    for (Stmt stmt : icfg.getNodes()) {
                        if (stmt instanceof LoadField loadField && loadField.isStatic()) {
                            if (field.equals(loadField.getFieldRef().resolve())) {
                                solver.getWorkList().add(loadField);
                            }
                        }
                    }
                }
                else if(storeField.getFieldAccess() instanceof InstanceFieldAccess access){
//                    System.out.println("-----------");
//                    System.out.println("store: " + storeField);
                    Var fieldBase = access.getBase();
                    for(Var alias : aliasMap.get(fieldBase)){
                        for (LoadField loadField : alias.getLoadFields()){
//                            System.out.println("load: " + loadField);
//                            System.out.println("storeField:" + field + " | " + "loadField:" + loadField.getFieldRef().resolve());
                            //why need check this?
                            if(field.equals(loadField.getFieldRef().resolve())) {
                                solver.getWorkList().add(loadField);
                            }
                        }
                    }
                }
            }
            return !origin.equals(out);
        }
        @Override
        public Boolean visit(LoadArray loadArray) {
            // y = x[i]
            CPFact origin = out.copy();
            out.copyFrom(in);

            Var left = loadArray.getLValue();
            Var loadIndex = loadArray.getArrayAccess().getIndex();
            Var loadBase = loadArray.getArrayAccess().getBase();

            if(ConstantPropagation.canHoldInt(left)) {
                Value leftValue = in.get(left);
                Value loadIndexValue = in.get(loadIndex);

                for (Var alias : aliasMap.get(loadBase)) {
                    for (StoreArray storeArray : alias.getStoreArrays()) {
                        Var right = storeArray.getRValue();
                        Var storeIndex = storeArray.getArrayAccess().getIndex();

                        Value rightValue = solver.getResult().getInFact(storeArray).get(right);
                        Value storeIndexValue = solver.getResult().getInFact(storeArray).get(storeIndex);
                        if (isArrayAlias(loadIndexValue, storeIndexValue)) {
                            leftValue = cp.meetValue(leftValue, rightValue);
                        }

                    }
                }
                out.update(left, leftValue);

                for(Stmt succ : icfg.getSuccsOf(loadArray)) {
                    solver.getWorkList().add(succ);
                }
            }
            return !origin.equals(out);
        }
        @Override
        public Boolean visit(StoreArray storeArray) {
            // x[i] = y
            CPFact origin = out.copy();
            out.copyFrom(in);

            Var right = storeArray.getRValue();
            Var storeIndex = storeArray.getArrayAccess().getIndex();
            Var storeBase = storeArray.getArrayAccess().getBase();

            if(ConstantPropagation.canHoldInt(right)){
                Value rightValue = in.get(right);
                Value storeIndexValue = in.get(storeIndex);

                for(Var alias : aliasMap.get(storeBase)){
                    for(LoadArray loadArray : alias.getLoadArrays()){
                        Var left = loadArray.getLValue();
                        Var loadIndex = loadArray.getArrayAccess().getIndex();
                        Value leftValue = solver.getResult().getInFact(loadArray).get(left);
                        Value loadIndexValue = solver.getResult().getInFact(loadArray).get(loadIndex);
                        if(isArrayAlias(storeIndexValue, loadIndexValue)){
                            solver.getWorkList().add(loadArray);
                        }
                    }
                }
            }
            return !origin.equals(out);
        }

    }

    @Override
    protected boolean transferNonCallNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        StmtProcessor processor = new StmtProcessor(in, out);
        return stmt.accept(processor);
    }

    @Override
    protected CPFact transferNormalEdge(NormalEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        return out.copy();
    }

    @Override
    protected CPFact transferCallToReturnEdge(CallToReturnEdge<Stmt> edge, CPFact out) {
        // TODO - finish me
        CPFact new_out = out.copy();
        Stmt callSite = edge.getSource();
        if (callSite instanceof Invoke invoke) {
            Var result = invoke.getResult();
            if (result != null) {
                new_out.remove(result);
            }
            return new_out;
        }
        assert false : "Unexpected call-to-return edge, call site is not an invoke statement";
        return null;
    }

    @Override
    protected CPFact transferCallEdge(CallEdge<Stmt> edge, CPFact callSiteOut) {
        // TODO - finish me
        CPFact new_out = new CPFact();
        Stmt callSite = edge.getSource();
        JMethod callee = edge.getCallee();
        if (callSite instanceof Invoke invoke) {
            List<Var> callSiteArgs = invoke.getInvokeExp().getArgs();
            List<Var> calleeParams = callee.getIR().getParams();
            for(int i = 0; i < callSiteArgs.size(); i++) {
                Var arg = callSiteArgs.get(i);
                Var param = calleeParams.get(i);
                new_out.update(param, callSiteOut.get(arg));
            }
            return new_out;
        }
        assert false : "Unexpected call edge, call site is not an invoke statement";
        return null;
    }

    @Override
    protected CPFact transferReturnEdge(ReturnEdge<Stmt> edge, CPFact returnOut) {
        // TODO - finish me
        CPFact new_out = new CPFact();
        Stmt callSite = edge.getCallSite();
        if (callSite instanceof Invoke invoke) {
            Var result = invoke.getResult();
            if (result != null) {
                Value value = Value.getUndef();
                for(Var returnVar : edge.getReturnVars()) {
                    value = cp.meetValue(value, returnOut.get(returnVar));
                }
                new_out.update(result, value);
            }
            return new_out;
        }
        assert false : "Unexpected return edge, call site is not an invoke statement";
        return null;
    }
}

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

package pascal.taie.analysis.dataflow.analysis;

import pascal.taie.analysis.MethodAnalysis;
import pascal.taie.analysis.dataflow.analysis.constprop.CPFact;
import pascal.taie.analysis.dataflow.analysis.constprop.ConstantPropagation;
import pascal.taie.analysis.dataflow.analysis.constprop.Value;
import pascal.taie.analysis.dataflow.fact.DataflowResult;
import pascal.taie.analysis.dataflow.fact.SetFact;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.graph.cfg.CFGBuilder;
import pascal.taie.analysis.graph.cfg.Edge;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.AssignStmt;
import pascal.taie.ir.stmt.If;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.ir.stmt.SwitchStmt;

import java.util.Comparator;
import java.util.Set;
import java.util.TreeSet;

import java.util.Queue;
import java.util.LinkedList;

public class DeadCodeDetection extends MethodAnalysis {

    public static final String ID = "deadcode";

    public DeadCodeDetection(AnalysisConfig config) {
        super(config);
    }

    @Override
    public Set<Stmt> analyze(IR ir) {
        // obtain CFG
        CFG<Stmt> cfg = ir.getResult(CFGBuilder.ID);
        // obtain result of constant propagation
        DataflowResult<Stmt, CPFact> constants =
                ir.getResult(ConstantPropagation.ID);
        // obtain result of live variable analysis
        DataflowResult<Stmt, SetFact<Var>> liveVars =
                ir.getResult(LiveVariableAnalysis.ID);
        // keep statements (dead code) sorted in the resulting set
        Set<Stmt> deadCode = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // TODO - finish me
        // Your task is to recognize dead code in ir and add it to deadCode

        // to store traversed stmt
        Set<Stmt> traversed = new TreeSet<>(Comparator.comparing(Stmt::getIndex));
        // add all stmt to deadCode for initialization
        deadCode.addAll(ir.getStmts());
        // if stmt is not dead, remove it from deadCode
        Queue<Stmt> worklist = new LinkedList<>();
        worklist.add(cfg.getEntry());
        while(!worklist.isEmpty()){
            Stmt stmt = worklist.poll();
            traversed.add(stmt);
            if(stmt instanceof If if_stmt){
                deadCode.remove(stmt);
                ConditionExp condition = if_stmt.getCondition();
                Value value = ConstantPropagation.evaluate(condition, constants.getInFact(stmt));
                // value can not be Undefined
                assert(value.isConstant() || value.isNAC());
                if(value.isConstant()){
                    // value only can be 0 or 1
                    assert(value.getConstant() == 0 || value.getConstant() == 1);
                    //tai-e ensure if_stmt has two edges -- IF_TRUE and IF_FALSE
                    if(value.getConstant() == 1){
                        for(Edge<Stmt> edge : cfg.getOutEdgesOf(if_stmt)){
                            if(edge.getKind() == Edge.Kind.IF_TRUE){
                                if(!worklist.contains(edge.getTarget()) && !traversed.contains(edge.getTarget())){
                                    worklist.add(edge.getTarget());
                                }
                            }
                        }
                    }
                    else if (value.getConstant() == 0){
                        for(Edge<Stmt> edge : cfg.getOutEdgesOf(if_stmt)){
                            if(edge.getKind() == Edge.Kind.IF_FALSE){
                                if(!worklist.contains(edge.getTarget()) && !traversed.contains(edge.getTarget())){
                                    worklist.add(edge.getTarget());
                                }
                            }
                        }
                    }
                    else{
                        assert false;
                    }
                }
                else if(value.isNAC()){
                    for(Stmt succ : cfg.getSuccsOf(stmt)){
                        if(!worklist.contains(succ) && !traversed.contains(succ)){
                            worklist.add(succ);
                        }
                    }
                }
            }
            else if(stmt instanceof SwitchStmt switch_stmt){
                deadCode.remove(stmt);
                Var var = switch_stmt.getVar();
                Value value = constants.getInFact(stmt).get(var);
                if(value.isConstant()) {
                    boolean flag = false;
                    for (Edge<Stmt> edge : cfg.getOutEdgesOf(switch_stmt)) {
                        if (edge.isSwitchCase()) {
                            if(edge.getCaseValue() == value.getConstant()){
                                if(!worklist.contains(edge.getTarget()) && !traversed.contains(edge.getTarget())){
                                    worklist.add(edge.getTarget());
                                }
                                flag = true;
                                break;
                            }
                        }
                    }
                    if(!flag){
                        Stmt default_target = switch_stmt.getDefaultTarget();
                        if (!worklist.contains(default_target) && !traversed.contains(default_target)) {
                            worklist.add(default_target);
                        }
                    }
                }
                else{
                    for(Stmt succ : cfg.getSuccsOf(stmt)){
                        if(!worklist.contains(succ) && !traversed.contains(succ)){
                            worklist.add(succ);
                        }
                    }
                }
            }
            else{
                if(stmt instanceof AssignStmt<?,?> assign_stmt) {
                    LValue lvalue = assign_stmt.getLValue();
                    RValue rvalue = assign_stmt.getRValue();
                    if(lvalue instanceof Var var){
                        if(liveVars.getOutFact(stmt).contains(var)) {
                            deadCode.remove(stmt);
                        }
                        if(!hasNoSideEffect(rvalue)) {
                            deadCode.remove(stmt);
                        }
                    }
                    else {
                        // lvalue is not Var, we do not care
                        deadCode.remove(stmt);
                    }
                }
                else{
                    // normal stmt
                    deadCode.remove(stmt);
                }
                for (Stmt succ : cfg.getSuccsOf(stmt)) {
                    if (!worklist.contains(succ) && !traversed.contains(succ)) {
                        worklist.add(succ);
                    }
                }
            }
        }
        return deadCode;
    }

    /**
     * @return true if given RValue has no side effect, otherwise false.
     */
    private static boolean hasNoSideEffect(RValue rvalue) {
        // new expression modifies the heap
        if (rvalue instanceof NewExp ||
                // cast may trigger ClassCastException
                rvalue instanceof CastExp ||
                // static field access may trigger class initialization
                // instance field access may trigger NPE
                rvalue instanceof FieldAccess ||
                // array access may trigger NPE
                rvalue instanceof ArrayAccess) {
            return false;
        }
        if (rvalue instanceof ArithmeticExp) {
            ArithmeticExp.Op op = ((ArithmeticExp) rvalue).getOperator();
            // may trigger DivideByZeroException
            return op != ArithmeticExp.Op.DIV && op != ArithmeticExp.Op.REM;
        }
        return true;
    }
}

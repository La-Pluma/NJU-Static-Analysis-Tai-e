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

package pascal.taie.analysis.dataflow.analysis.constprop;

import pascal.taie.analysis.dataflow.analysis.AbstractDataflowAnalysis;
import pascal.taie.analysis.graph.cfg.CFG;
import pascal.taie.analysis.pta.PointerAnalysisResult;
import pascal.taie.analysis.pta.core.heap.Obj;
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;
import pascal.taie.util.collection.Maps;
import pascal.taie.util.collection.MultiMap;

public class ConstantPropagation extends
        AbstractDataflowAnalysis<Stmt, CPFact> {

    public static final String ID = "constprop";

    public ConstantPropagation(AnalysisConfig config) {
        super(config);
    }

    @Override
    public boolean isForward() {
        return true;
    }

    @Override
    public CPFact newBoundaryFact(CFG<Stmt> cfg) {
        // TODO - finish me
        CPFact fact = new CPFact();
        for(Var var : cfg.getIR().getParams()){
            if(canHoldInt(var)){
                fact.update(var, Value.getNAC());
            }
        }
        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        // TODO - finish me
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        // TODO - finish me
        for(Var var : fact.keySet()){
            target.update(var, meetValue(fact.get(var), target.get(var)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        // TODO - finish me
        if(v1.isNAC() || v2.isNAC()){
            return Value.getNAC();
        }
        if(v1.isUndef()){
            return v2;
        }
        if(v2.isUndef()){
            return v1;
        }
        if(v1.isConstant() && v2.isConstant()){
            if(v1.getConstant() == v2.getConstant()){
                return Value.makeConstant(v1.getConstant());
            }
            return Value.getNAC();
        }
        //not reach here
        return Value.getNAC();
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        // TODO - finish me
        CPFact origin = out.copy();
        out.copyFrom(in);
        //we only need to handle definition statement
        if(stmt instanceof DefinitionStmt<?, ?> def_stmt){
            LValue def = def_stmt.getLValue();
            if (def != null) {
                if(def instanceof Var var && canHoldInt(var)){
                    Exp exp = def_stmt.getRValue(); // RValue extends Exp
                    Value value = evaluate(exp, in);
                    out.update(var, value);
                }
                // we do not need to handle not Var def & Var that cannot hold int
            }
            // o.f = x equals nop
        }
        //not a definition statement, equals nop

        return !origin.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE:
                case SHORT:
                case INT:
                case CHAR:
                case BOOLEAN:
                    return true;
            }
        }
        return false;
    }

    /**
     * Evaluates the {@link Value} of given expression.
     *
     * @param exp the expression to be evaluated
     * @param in  IN fact of the statement
     * @return the resulting {@link Value}
     */
    public static Value evaluate(Exp exp, CPFact in) {
        // TODO - finish me
        if (exp instanceof Var var) {
            if(canHoldInt(var)){
                return in.get(var);
            }
            return Value.getNAC();
        }
        else if(exp instanceof IntLiteral intliteral) {
            //we can ensure that intliteral is a constant
            return Value.makeConstant(intliteral.getValue());
        }
        else if(exp instanceof BinaryExp binary_exp) {
            Var left = binary_exp.getOperand1();
            Var right = binary_exp.getOperand2();
            // there maybe some other types in binary expression
            if(canHoldInt(left) && canHoldInt(right)) {
                if (in.get(left).isNAC() || in.get(right).isNAC()) {
                    // attention to / and % when right is 0
                    if(binary_exp instanceof ArithmeticExp arithmetic_exp){
                        ArithmeticExp.Op op = arithmetic_exp.getOperator();
                        if(op == ArithmeticExp.Op.DIV || op == ArithmeticExp.Op.REM){
                            if(in.get(right).isConstant() && in.get(right).getConstant() == 0){
                                return Value.getUndef();
                            }
                        }
                    }
                    return Value.getNAC();
                }
                if(in.get(left).isConstant() && in.get(right).isConstant()){
                    int left_value = in.get(left).getConstant();
                    int right_value = in.get(right).getConstant();
                    if (binary_exp instanceof ArithmeticExp arithmetic_exp) {
                        ArithmeticExp.Op op = arithmetic_exp.getOperator();
                        switch (op) {
                            case ADD -> {
                                return Value.makeConstant(left_value + right_value);
                            }
                            case SUB -> {
                                return Value.makeConstant(left_value - right_value);
                            }
                            case MUL -> {
                                return Value.makeConstant(left_value * right_value);
                            }
                            case DIV -> {
                                if(right_value == 0){
                                    return Value.getUndef();
                                }
                                return Value.makeConstant(left_value / right_value);
                            }
                            case REM -> {
                                if (right_value == 0) {
                                    return Value.getUndef();
                                }
                                return Value.makeConstant(left_value % right_value);
                            }
                        }
                    } else if (binary_exp instanceof BitwiseExp bitwise_exp) {
                        BitwiseExp.Op op = bitwise_exp.getOperator();
                        switch (op) {
                            case AND -> {
                                return Value.makeConstant(left_value & right_value);
                            }
                            case OR -> {
                                return Value.makeConstant(left_value | right_value);
                            }
                            case XOR -> {
                                return Value.makeConstant(left_value ^ right_value);
                            }
                        }

                    } else if (binary_exp instanceof ConditionExp condition_exp) {
                        ConditionExp.Op op = condition_exp.getOperator();
                        switch (op) {
                            case EQ -> {
                                return Value.makeConstant(left_value == right_value ? 1 : 0);
                            }
                            case NE -> {
                                return Value.makeConstant(left_value != right_value ? 1 : 0);
                            }
                            case LT -> {
                                return Value.makeConstant(left_value < right_value ? 1 : 0);
                            }
                            case LE -> {
                                return Value.makeConstant(left_value <= right_value ? 1 : 0);
                            }
                            case GT -> {
                                return Value.makeConstant(left_value > right_value ? 1 : 0);
                            }
                            case GE -> {
                                return Value.makeConstant(left_value >= right_value ? 1 : 0);
                            }
                        }
                    } else if (binary_exp instanceof ShiftExp shift_exp) {
                        ShiftExp.Op op = shift_exp.getOperator();
                        switch (op) {
                            case SHL -> {
                                return Value.makeConstant(left_value << right_value);
                            }
                            case SHR -> {
                                return Value.makeConstant(left_value >> right_value);
                            }
                            case USHR -> {
                                return Value.makeConstant(left_value >>> right_value);
                            }
                        }
                    }
                    return Value.getNAC();
                }
                if(in.get(left).isUndef() || in.get(right).isUndef()) {
                    return Value.getUndef();
                }
                return Value.getUndef();
            }
            return Value.getNAC();
        }
        //for safe-approximation
        return Value.getNAC();
    }
}

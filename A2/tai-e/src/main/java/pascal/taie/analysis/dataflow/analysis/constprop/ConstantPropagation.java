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
import pascal.taie.config.AnalysisConfig;
import pascal.taie.ir.IR;
import pascal.taie.ir.exp.*;
import pascal.taie.ir.stmt.DefinitionStmt;
import pascal.taie.ir.stmt.Stmt;
import pascal.taie.language.type.PrimitiveType;
import pascal.taie.language.type.Type;
import pascal.taie.util.AnalysisException;

import java.util.Objects;

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
        CPFact fact = new CPFact();

        for (Var i : cfg.getIR().getParams()) {
            if (canHoldInt(i)) {
                fact.update(i, Value.getNAC());
            }
        }

        return fact;
    }

    @Override
    public CPFact newInitialFact() {
        return new CPFact();
    }

    @Override
    public void meetInto(CPFact fact, CPFact target) {
        for (Var i : fact.keySet()) {
            target.update(i, meetValue(fact.get(i), target.get(i)));
        }
    }

    /**
     * Meets two Values.
     */
    public Value meetValue(Value v1, Value v2) {
        if (v1.isNAC() || v2.isUndef()) {
            return v1;
        } else if (v1.isUndef() || v2.isNAC()) {
            return v2;
        } else if (v1.equals(v2)) {
            return v1;
        } else {
            return Value.getNAC();
        }
    }

    @Override
    public boolean transferNode(Stmt stmt, CPFact in, CPFact out) {
        CPFact oldOut = out.copy();
        out.clear();
        out = in.copy();

        if (stmt instanceof DefinitionStmt<?,?> dStmt) {
            LValue lv = dStmt.getLValue();
            RValue rv = dStmt.getRValue();

            if (lv instanceof Var vLv && canHoldInt(vLv)) {
                out.update(vLv, evaluate(rv, in));
            }
        }

        return !oldOut.equals(out);
    }

    /**
     * @return true if the given variable can hold integer value, otherwise false.
     */
    public static boolean canHoldInt(Var var) {
        Type type = var.getType();
        if (type instanceof PrimitiveType) {
            switch ((PrimitiveType) type) {
                case BYTE, SHORT, INT, CHAR, BOOLEAN -> {
                    return true;
                }
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
        if (exp instanceof Var vExp) {
            return in.get(vExp);
        } else if (exp instanceof IntLiteral iExp) {
            return Value.makeConstant(iExp.getValue());
        } else if (exp instanceof BinaryExp bExp) {
            BinaryExp.Op operator = bExp.getOperator();
            Value val1 = in.get(bExp.getOperand1());
            Value val2 = in.get(bExp.getOperand2());

            if (operator.toString().equals("/") || operator.toString().equals("%")) {
                if (val2.isConstant() && val2.getConstant() == 0) {
                    return Value.getUndef();
                }
            }

            if (val1.isConstant() &&val2.isConstant()) {
                return calculate(val1.getConstant(), val2.getConstant(), operator.toString());
            } else if (val1.isNAC() || val2.isNAC()) {
                return Value.getNAC();
            } else {
                return Value.getUndef();
            }
        } else {
            return Value.getNAC();
        }
    }

    private static Value calculate(int a, int b, String op) {
        int flag = switch (op) {
            // ArithmeticExp
            case "+" -> a + b;
            case "-" -> a - b;
            case "*" -> a * b;
            case "/" -> a / b;
            case "%" -> a % b;
            // ConditionExp
            case "==" -> a == b ? 1 : 0;
            case "!=" -> a != b ? 1 : 0;
            case ">" -> a > b ? 1 : 0;
            case ">=" -> a >= b ? 1 : 0;
            case "<" -> a < b ? 1 : 0;
            case "<=" -> a <= b ? 1 : 0;
            // BitwiseExp
            case "&" -> a & b;
            case "|" -> a | b;
            case "^" -> a ^ b;
            // ShiftExp
            case ">>" -> a >> b;
            case "<<" -> a << b;
            case ">>>" -> a >>> b;
            default -> throw new RuntimeException("Unknown Operator: " + op + ".");
        };

        return Value.makeConstant(flag);
    }

}

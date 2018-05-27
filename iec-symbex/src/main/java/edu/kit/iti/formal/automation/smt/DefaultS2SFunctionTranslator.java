package edu.kit.iti.formal.automation.smt;

/*-
 * #%L
 * iec-symbex
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import de.tudresden.inf.lat.jsexp.Sexp;
import edu.kit.iti.formal.smv.EnumType;
import edu.kit.iti.formal.smv.SMVType;
import edu.kit.iti.formal.smv.SMVTypes;
import edu.kit.iti.formal.smv.SMVWordType;
import edu.kit.iti.formal.smv.ast.SBinaryOperator;
import edu.kit.iti.formal.smv.ast.SFunction;
import edu.kit.iti.formal.smv.ast.SUnaryOperator;

import javax.annotation.Nonnull;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static de.tudresden.inf.lat.jsexp.SexpFactory.newAtomicSexp;

/**
 * http://smtlib.cs.uiowa.edu/Logics/QF_BV.smt2
 *
 * @author Alexander Weigl
 * @version 1 (15.10.17)
 */
public class DefaultS2SFunctionTranslator implements S2SFunctionTranslator {
    static Map<SBinaryOperator, String> logicalOperators = new HashMap<>();
    static Map<SBinaryOperator, String> bvuOperators = new HashMap<>();
    static Map<SBinaryOperator, String> bvsOperators = new HashMap<>();
    static Map<SBinaryOperator, String> arithOperators = new HashMap<>();

    static {
        logicalOperators.put(SBinaryOperator.AND, "and");
        logicalOperators.put(SBinaryOperator.OR, "or");
        logicalOperators.put(SBinaryOperator.IMPL, "impl");
        logicalOperators.put(SBinaryOperator.EQUAL, "=");
        logicalOperators.put(SBinaryOperator.NOT_EQUAL, "xor");
        logicalOperators.put(SBinaryOperator.XOR, "xor");
        logicalOperators.put(SBinaryOperator.XNOR, "=");

        bvsOperators.put(SBinaryOperator.MUL, "bvmul");
        bvsOperators.put(SBinaryOperator.PLUS, "bvadd");
        bvsOperators.put(SBinaryOperator.MUL, "bvmull");
        bvsOperators.put(SBinaryOperator.DIV, "bvsdiv");
        bvsOperators.put(SBinaryOperator.XOR, "bvxor");
        bvsOperators.put(SBinaryOperator.XNOR, "bvxnor");
        bvsOperators.put(SBinaryOperator.EQUAL, "=");
        bvsOperators.put(SBinaryOperator.MINUS, "bvsub");
        bvsOperators.put(SBinaryOperator.MOD, "bvsmod");
        bvsOperators.put(SBinaryOperator.GREATER_EQUAL, "bvsge");
        bvsOperators.put(SBinaryOperator.GREATER_THAN, "bvsgt");
        bvsOperators.put(SBinaryOperator.LESS_EQUAL, "bvsle");
        bvsOperators.put(SBinaryOperator.LESS_THAN, "bvslt");
        bvsOperators.put(SBinaryOperator.NOT_EQUAL, "<>");

        bvuOperators.put(SBinaryOperator.NOT_EQUAL, "<>");
        bvuOperators.put(SBinaryOperator.MUL, "bvmul");
        bvuOperators.put(SBinaryOperator.PLUS, "bvadd");
        bvuOperators.put(SBinaryOperator.DIV, "bvudiv");
        bvuOperators.put(SBinaryOperator.XOR, "bvxor");
        bvuOperators.put(SBinaryOperator.EQUAL, "=");
        bvuOperators.put(SBinaryOperator.XNOR, "bvxnor");
        bvuOperators.put(SBinaryOperator.MINUS, "bvsub");
        bvuOperators.put(SBinaryOperator.MOD, "bvurem");
        bvuOperators.put(SBinaryOperator.GREATER_EQUAL, "bvuge");
        bvuOperators.put(SBinaryOperator.GREATER_THAN, "bvugt");
        bvuOperators.put(SBinaryOperator.LESS_EQUAL, "bvule");
        bvuOperators.put(SBinaryOperator.LESS_THAN, "bvult");

    }

    @Override
    @Nonnull
    public Sexp translateOperator(@Nonnull SBinaryOperator operator, @Nonnull SMVType typeLeft, @Nonnull SMVType rightType) {
        String defaultValue = "not-found-operator-" + operator.symbol();

        if (typeLeft == SMVTypes.BOOLEAN.INSTANCE) {
            return newAtomicSexp(logicalOperators.getOrDefault(operator,
                    defaultValue));
        }

        if (typeLeft instanceof SMVWordType) {
            SMVWordType left = (SMVWordType) typeLeft;
            if (left.getSigned())
                return newAtomicSexp(bvsOperators.getOrDefault(operator, defaultValue));
            else
                return newAtomicSexp(bvuOperators.getOrDefault(operator, defaultValue));
        }

        if (typeLeft instanceof EnumType) {
            return newAtomicSexp(bvuOperators.getOrDefault(operator, defaultValue));
        }

        throw new IllegalArgumentException();
    }

    @Override
    public Sexp translateOperator(SUnaryOperator operator, SMVType type) {
        Sexp bvneg = newAtomicSexp("bvneg");
        Sexp not = newAtomicSexp("not");
        switch (operator) {
            case MINUS:
                return bvneg;
            case NEGATE:
                return not;
        }
        throw new IllegalArgumentException();
    }

    @Override
    public Sexp translateOperator(SFunction func, List<Sexp> args) {
        //TODO translation of various functions
        return null;
    }
}

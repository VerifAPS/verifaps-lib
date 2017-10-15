package edu.kit.iti.formal.automation.smt;

import de.tudresden.inf.lat.jsexp.Sexp;
import edu.kit.iti.formal.smv.ast.*;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static de.tudresden.inf.lat.jsexp.SexpFactory.newAtomicSexp;
import static edu.kit.iti.formal.smv.ast.GroundDataType.BOOLEAN;

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
        logicalOperators.put(SBinaryOperator.XOR, "xor");
        logicalOperators.put(SBinaryOperator.XNOR, "=");

        bvsOperators.put(SBinaryOperator.MUL, "bvmul");
        bvsOperators.put(SBinaryOperator.PLUS, "bvadd");
        bvsOperators.put(SBinaryOperator.MUL, "bvmull");
        bvsOperators.put(SBinaryOperator.DIV, "bvsdiv");
        bvsOperators.put(SBinaryOperator.XOR, "bvxor");
        bvsOperators.put(SBinaryOperator.XNOR, "bvxnor");
        bvsOperators.put(SBinaryOperator.EQUAL, "bvcomp"); //NOT RETURN BOOL
        bvsOperators.put(SBinaryOperator.MINUS, "bvsub");
        bvsOperators.put(SBinaryOperator.MOD, "bvsmod");
        bvsOperators.put(SBinaryOperator.GREATER_EQUAL, "bvsge");
        bvsOperators.put(SBinaryOperator.GREATER_THAN, "bvsgt");
        bvsOperators.put(SBinaryOperator.LESS_EQUAL, "bvsle");
        bvsOperators.put(SBinaryOperator.LESS_THAN, "bvslt");

        bvuOperators.put(SBinaryOperator.MUL, "bvmul");
        bvuOperators.put(SBinaryOperator.PLUS, "bvadd");
        bvuOperators.put(SBinaryOperator.DIV, "bvudiv");
        bvuOperators.put(SBinaryOperator.XOR, "bvxor");
        bvuOperators.put(SBinaryOperator.EQUAL, "bvcomp");
        bvuOperators.put(SBinaryOperator.XNOR, "bvxnor");
        bvuOperators.put(SBinaryOperator.MINUS, "bvsub");
        bvuOperators.put(SBinaryOperator.MOD, "bvurem");
        bvuOperators.put(SBinaryOperator.GREATER_EQUAL, "bvuge");
        bvuOperators.put(SBinaryOperator.GREATER_THAN, "bvugt");
        bvuOperators.put(SBinaryOperator.LESS_EQUAL, "bvule");
        bvuOperators.put(SBinaryOperator.LESS_THAN, "bvult");

    }

    @Override
    public Sexp translateOperator(SBinaryOperator operator, SMVType typeLeft, SMVType rightType) {
        String defaultValue = "not-found-operator-" + operator.symbol();

        if (typeLeft.getBaseType() == BOOLEAN) {
            return newAtomicSexp(logicalOperators.getOrDefault(operator,
                    defaultValue));
        }

        if (typeLeft.getBaseType() == GroundDataType.SIGNED_WORD) {
            return newAtomicSexp(bvsOperators.getOrDefault(operator, defaultValue));
        }

        if (typeLeft.getBaseType() == GroundDataType.UNSIGNED_WORD) {
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

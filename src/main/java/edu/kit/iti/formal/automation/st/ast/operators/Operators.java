package edu.kit.iti.formal.automation.st.ast.operators;

import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.AnyNum;
import edu.kit.iti.formal.automation.st.ast.UnaryExpression;

import java.util.HashMap;
import java.util.Map;

import static edu.kit.iti.formal.automation.datatypes.AnyNum.ANY_NUM;

/**
 * Created by weigl on 24.11.16.
 */
public class Operators {
    public static UnaryOperator NOT = new UnaryOperator("NOT", AnyBit.BOOL);
    public static UnaryOperator MINUS = new UnaryOperator("-", ANY_NUM);

    public static BinaryOperator ADD = new BinaryOperator("+", ANY_NUM);

    public static BinaryOperator MULT = new BinaryOperator("*", ANY_NUM);

    public static BinaryOperator SUB = new BinaryOperator("-", ANY_NUM);

    public static BinaryOperator DIV = new BinaryOperator("/", ANY_NUM);

    public static BinaryOperator MOD = new BinaryOperator("MOD", ANY_NUM);

    public static BinaryOperator AND = new BinaryOperator("AND", AnyBit.BOOL);

    public static BinaryOperator OR = new BinaryOperator("OR", AnyBit.BOOL);

    public static BinaryOperator XOR = new BinaryOperator("XOR", AnyBit.BOOL);

    public static BinaryOperator POWER = new BinaryOperator("**", new AnyNum());

    // Comparison
    public static ComparisonOperator EQUALS = new ComparisonOperator("=");
    public static ComparisonOperator NOT_EQUALS = new ComparisonOperator("<>");
    public static ComparisonOperator LESS_THAN = new ComparisonOperator("<");
    public static ComparisonOperator GREATER_THAN = new ComparisonOperator(">");
    public static ComparisonOperator GREATER_EQUALS = new ComparisonOperator(">=");
    public static ComparisonOperator LESS_EQUALS = new ComparisonOperator("<=");


    //
    private static Map<String, Operator> TABLE = new HashMap<>();

    public static Operator lookup(String operator) {
        return TABLE.get(operator);
    }

    public static void register(String symbol, Operator op) {
        TABLE.put(symbol, op);
    }
}

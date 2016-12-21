package edu.kit.iti.formal.automation.operators;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.datatypes.AnyNum;

import java.util.HashMap;
import java.util.Map;

import static edu.kit.iti.formal.automation.datatypes.AnyNum.ANY_NUM;

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class Operators {
    /** Constant <code>NOT</code> */
    public static UnaryOperator NOT = new UnaryOperator("NOT", AnyBit.BOOL);
    /** Constant <code>MINUS</code> */
    public static UnaryOperator MINUS = new UnaryOperator("-", ANY_NUM);

    /** Constant <code>ADD</code> */
    public static BinaryOperator ADD = new BinaryOperator("+", ANY_NUM);

    /** Constant <code>MULT</code> */
    public static BinaryOperator MULT = new BinaryOperator("*", ANY_NUM);

    /** Constant <code>SUB</code> */
    public static BinaryOperator SUB = new BinaryOperator("-", ANY_NUM);

    /** Constant <code>DIV</code> */
    public static BinaryOperator DIV = new BinaryOperator("/", ANY_NUM);

    /** Constant <code>MOD</code> */
    public static BinaryOperator MOD = new BinaryOperator("MOD", ANY_NUM);

    /** Constant <code>AND</code> */
    public static BinaryOperator AND = new BinaryOperator("AND", AnyBit.BOOL);

    /** Constant <code>OR</code> */
    public static BinaryOperator OR = new BinaryOperator("OR", AnyBit.BOOL);

    /** Constant <code>XOR</code> */
    public static BinaryOperator XOR = new BinaryOperator("XOR", AnyBit.BOOL);

    /** Constant <code>POWER</code> */
    public static BinaryOperator POWER = new BinaryOperator("**", new AnyNum());

    // Comparison
    /** Constant <code>EQUALS</code> */
    public static ComparisonOperator EQUALS = new ComparisonOperator("=");
    /** Constant <code>NOT_EQUALS</code> */
    public static ComparisonOperator NOT_EQUALS = new ComparisonOperator("<>");
    /** Constant <code>LESS_THAN</code> */
    public static ComparisonOperator LESS_THAN = new ComparisonOperator("<");
    /** Constant <code>GREATER_THAN</code> */
    public static ComparisonOperator GREATER_THAN = new ComparisonOperator(">");
    /** Constant <code>GREATER_EQUALS</code> */
    public static ComparisonOperator GREATER_EQUALS = new ComparisonOperator(">=");
    /** Constant <code>LESS_EQUALS</code> */
    public static ComparisonOperator LESS_EQUALS = new ComparisonOperator("<=");


    //
    private static Map<String, Operator> TABLE;

    /**
     * <p>lookup.</p>
     *
     * @param operator a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.operators.Operator} object.
     */
    public static Operator lookup(String operator) {
        return TABLE.get(operator);
    }

    /**
     * <p>register.</p>
     *
     * @param symbol a {@link java.lang.String} object.
     * @param op a {@link edu.kit.iti.formal.automation.operators.Operator} object.
     */
    public static void register(String symbol, Operator op) {
        if (TABLE == null) TABLE = new HashMap<>();
        TABLE.put(symbol, op);
    }
}

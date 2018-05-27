package edu.kit.iti.formal.automation.operators

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.AnyBit
import edu.kit.iti.formal.automation.datatypes.AnyNum

import java.util.HashMap

import edu.kit.iti.formal.automation.datatypes.AnyNum.ANY_NUM

/**
 * Facade.
 *
 *
 *
 *
 *
 * Created on 24.11.16.
 *
 * @author Alexander Weigl
 * @version 1
 */
object Operators {
    /**
     * Constant `NOT`
     */
    var NOT = UnaryOperator("NOT", AnyBit.BOOL)
    /**
     * Constant `MINUS`
     */
    var MINUS = UnaryOperator("-", ANY_NUM)

    /**
     * Constant `ADD`
     */
    var ADD = BinaryOperator("+", ANY_NUM)

    /**
     * Constant `MULT`
     */
    var MULT = BinaryOperator("*", ANY_NUM)

    /**
     * Constant `SUB`
     */
    var SUB = BinaryOperator("-", ANY_NUM)

    /**
     * Constant `DIV`
     */
    var DIV = BinaryOperator("/", ANY_NUM)

    /**
     * Constant `MOD`
     */
    var MOD = BinaryOperator("MOD", ANY_NUM)

    /**
     * Constant `AND`
     */
    var AND = BinaryOperator("AND", AnyBit.BOOL)

    /**
     * Constant `OR`
     */
    var OR = BinaryOperator("OR", AnyBit.BOOL)

    /**
     * Constant `XOR`
     */
    var XOR = BinaryOperator("XOR", AnyBit.BOOL)

    /**
     * Constant `POWER`
     */
    var POWER = BinaryOperator("**", AnyNum())

    // Comparison
    /**
     * Constant `EQUALS`
     */
    var EQUALS = ComparisonOperator("=")
    /**
     * Constant `NOT_EQUALS`
     */
    var NOT_EQUALS = ComparisonOperator("<>")
    /**
     * Constant `LESS_THAN`
     */
    var LESS_THAN = ComparisonOperator("<")
    /**
     * Constant `GREATER_THAN`
     */
    var GREATER_THAN = ComparisonOperator(">")
    /**
     * Constant `GREATER_EQUALS`
     */
    var GREATER_EQUALS = ComparisonOperator(">=")
    /**
     * Constant `LESS_EQUALS`
     */
    var LESS_EQUALS = ComparisonOperator("<=")


    //
    private var TABLE: MutableMap<String, Operator>? = null

    /**
     *
     * lookup.
     *
     * @param operator a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.operators.Operator] object.
     */
    fun lookup(operator: String): Operator {
        return TABLE!![operator]
    }

    /**
     *
     * register.
     *
     * @param symbol a [java.lang.String] object.
     * @param op     a [edu.kit.iti.formal.automation.operators.Operator] object.
     */
    fun register(symbol: String, op: Operator) {
        if (TABLE == null) TABLE = HashMap()
        TABLE!![symbol] = op
    }
}

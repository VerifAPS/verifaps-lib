package edu.kit.iti.formal.automation.operators

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
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
import java.util.*

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
    val NOT = UnaryOperator("NOT", AnyBit.BOOL)
    val MINUS = UnaryOperator("-", AnyNum.ANY_NUM)
    val ADD = BinaryOperator("+", AnyNum.ANY_NUM)
    val MULT = BinaryOperator("*", AnyNum.ANY_NUM)
    val SUB = BinaryOperator("-", AnyNum.ANY_NUM)
    val DIV = BinaryOperator("/", AnyNum.ANY_NUM)
    val MOD = BinaryOperator("MOD", AnyNum.ANY_NUM)
    val AND = BooleanOperator("AND")
    val OR = BooleanOperator("OR")
    val XOR = BooleanOperator("XOR")
    val POWER = BinaryOperator("**", AnyNum())
    // Comparison
    val EQUALS = ComparisonOperator("=")
    val NOT_EQUALS = ComparisonOperator("<>")
    val LESS_THAN = ComparisonOperator("<")
    val GREATER_THAN = ComparisonOperator(">")
    val GREATER_EQUALS = ComparisonOperator(">=")
    val LESS_EQUALS = ComparisonOperator("<=")
    //

    private val TABLE: MutableMap<String, Operator> = mutableMapOf()

    init {
        register(NOT)
        register(MINUS)
        register(ADD)
        register(MULT)
        register(SUB)
        register(DIV)
        register(MOD)
        register(AND)
        register(OR)
        register(XOR)
        register(POWER)
        register(EQUALS)
        register(NOT_EQUALS)
        register(LESS_THAN)
        register(GREATER_THAN)
        register(GREATER_EQUALS)
        register(LESS_EQUALS)

    }

    fun lookup(operator: String): Operator {
        if (operator.uppercase(Locale.getDefault()) !in TABLE) {
            throw IllegalArgumentException("Operator $operator is not defined")
        }
        return TABLE[operator.uppercase(Locale.getDefault())]!!
    }

    fun register(op: Operator) = register(op.symbol, op)
    fun register(symbol: String, op: Operator) {
        TABLE[symbol] = op
    }
}

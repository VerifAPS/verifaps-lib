// --------------------------------------------------------
// Code generated by Papyrus Java
// --------------------------------------------------------

package edu.kit.iti.formal.smv.ast;

/*-
 * #%L
 * smv-model
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

/*
 * The order of parsing precedence for operators from high to low is:
 * 0: [ ] , [ : ]
 * 1: !
 * 2: ::
 * 3: - (unary minus)
 * 4: /
 * 6: mod
 * 7: *
 * 8: + -
 * 9: << >>
 * 10: union
 * 11: in
 * 12: = !=  <  >
 * 13: &
 * 14: | xor xnor
 * 15: (• ? • : •)
 * 16: <->
 * 17: ->
 */
public enum SBinaryOperator implements SOperator {
    /**
     *
     */
    PLUS("+", 8),
    /**
     *
     */
    MINUS("-", 8),
    /**
     *
     */
    DIV("/", 4),
    /**
     *
     */
    MUL("*", 6),
    /**
     *
     */
    AND("&", 13),
    /**
     *
     */
    OR("|", 14),
    /**
     *
     */
    LESS_THAN("<", 12),
    /**
     *
     */
    LESS_EQUAL("<=", 12),
    /**
     *
     */
    GREATER_THAN(">", 12),
    /**
     *
     */
    GREATER_EQUAL(">=", 12),
    /**
     *
     */
    XOR("xor", 14),

    /**
     *
     */
    XNOR("xnor", 14),

    /**
     *
     */
    EQUAL("=", 12),

    /**
     *
     */
    IMPL("->", 17),

    /**
     *
     */
    EQUIV("<->", 16),

    /**
     *
     */
    NOT_EQUAL("!=", 12),

    /**
     *
     */
    MOD("mod", 5),

    /**
     *
     */
    SHL("<<", 9),

    /**
     *
     */
    SHR(">>", 9);

    private final int precedence;
    private final String symbol;

    SBinaryOperator(String symbol, int p) {
        this.symbol = symbol;
        precedence = p;
    }

    @Override
    public int precedence() {
        return precedence;
    }

    public String symbol() {
        return symbol;
    }

    public static SBinaryOperator findBySymbol(String symbol) {
        for (SBinaryOperator op :
                values()) {
            if (op.symbol.equalsIgnoreCase(symbol)) {
                return op;
            }
        }
        return null;
    }
}
package edu.kit.iti.formal.smv.ast;

/*-
 * #%L
 * smv-model
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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import org.antlr.v4.runtime.Token;

/**
 * @author Alexander Weigl
 * @version 1 (11.06.17)
 */
public enum STemporalOperator {
    X(TemporalLanguage.LTL, 1, "X", "NEXT"),
    G(TemporalLanguage.LTL, 1, "G", "GLOBALLY"),
    F(TemporalLanguage.LTL, 1, "F", "FINALLY"),
    Y(TemporalLanguage.LTL, 1, "Y", "YESTERDAY"),
    Z(TemporalLanguage.LTL, 1, "Z", "?"),
    H(TemporalLanguage.LTL, 1, "H", "?"),
    O(TemporalLanguage.LTL, 1, "O", "ONCE"),

    U(TemporalLanguage.LTL, 2, "U", "UNTIL"),
    V(TemporalLanguage.LTL, 2, "V", "RELEASE"),
    S(TemporalLanguage.LTL, 2, "S", "SINCE"),
    T(TemporalLanguage.LTL, 2, "T", "?"),

    AU(TemporalLanguage.CTL, 2, "AU", ""),
    EU(TemporalLanguage.CTL, 2, "EU", ""),

    EG(TemporalLanguage.CTL, 2, "EG", ""),
    EF(TemporalLanguage.CTL, 2, "EF", ""),
    EX(TemporalLanguage.CTL, 2, "EX", ""),
    AG(TemporalLanguage.CTL, 2, "AG", ""),
    AF(TemporalLanguage.CTL, 2, "AF", ""),
    AX(TemporalLanguage.CTL, 2, "AX", "");

    private final String name;
    private final String symbol;
    private final int arity;
    private final TemporalLanguage language;

    private STemporalOperator(TemporalLanguage l, int arity, String symbol, String name) {
        this.language = l;
        this.arity = arity;
        this.symbol = symbol;
        this.name = name;
    }

    public static STemporalOperator valueOf(Token op) {
        return valueOf(op.getText());
    }

    public int arity() {
        return arity;
    }

    public String symbol() {
        return symbol;
    }

    private enum TemporalLanguage {
        LTL, CTL, PSL
    }
}

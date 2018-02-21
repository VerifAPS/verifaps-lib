package edu.kit.iti.formal.automation.sfclang.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2017 - 2018 Alexander Weigl
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

import edu.kit.iti.formal.automation.st.ast.Expression;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * @author Alexander Weigl
 * @version 1 (30.01.18)
 */
@Data
@NoArgsConstructor
@AllArgsConstructor
public class SFCActionQualifier {
    public static SFCActionQualifier RAISING = new SFCActionQualifier(Qualifier.RAISING);
    public static SFCActionQualifier FALLING = new SFCActionQualifier(Qualifier.FALLING);
    public static SFCActionQualifier NON_STORED = new SFCActionQualifier(Qualifier.NON_STORED);
    public static SFCActionQualifier OVERRIDING_RESET = new SFCActionQualifier(Qualifier.OVERRIDING_RESET);
    public static SFCActionQualifier SET = new SFCActionQualifier(Qualifier.SET);

    private Qualifier qualifier;
    private Expression time;

    public SFCActionQualifier(Qualifier qq) {
        qualifier = qq;
    }

    public SFCActionQualifier(String qName) {
        try {
            qualifier = SFCActionQualifier.Qualifier.valueOf(qName);
        } catch (IllegalArgumentException e) {
            for (Qualifier q : Qualifier.values()) {
                if (q.symbol.equals(qName)) {
                    qualifier = q;
                    break;
                }
            }
        }
    }

    public boolean hasTime() {
        return qualifier.hasTime;
    }

    public SFCActionQualifier copy() {
        SFCActionQualifier q = new SFCActionQualifier();
        q.qualifier = qualifier;
        q.time = time.copy();
        return q;
    }

    public enum Qualifier {
        NON_STORED("N", false),
        OVERRIDING_RESET("R", false),
        SET("S", false),
        TIME_LIMITED("L", true),
        STORE_AND_DELAY("SD", true),
        STORE_AND_LIMITED("SL", true),
        STORE_DELAYED("D", true),
        DELAYED_AND_STORED("DS", true),
        RAISING("P1 ", false),
        FALLING("P0", false);

        public final String symbol;
        public final boolean hasTime;

        Qualifier(String symbol, boolean hasTime) {
            this.symbol = symbol;
            this.hasTime = hasTime;
        }
    }

}

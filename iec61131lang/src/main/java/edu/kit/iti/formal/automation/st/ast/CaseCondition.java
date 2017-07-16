package edu.kit.iti.formal.automation.st.ast;

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

import edu.kit.iti.formal.automation.visitors.Utils;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.AllArgsConstructor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.ToString;

/**
 * <p>Abstract CaseCondition class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public abstract class CaseCondition extends Top {
    public abstract CaseCondition copy();

    @Data
    @AllArgsConstructor
    @EqualsAndHashCode
    @ToString
    public static class Range extends CaseCondition {
        private Literal start, stop;

        public <T> T accept(Visitor<T> visitor) {
            return visitor.visit(this);
        }

        @Override
        public Range copy() {
            Range r = new Range(start.copy(), Utils.copyNull(stop));
            r.setRuleContext(getRuleContext());
            return r;
        }
    }

    @AllArgsConstructor
    @ToString
    @Data
    @EqualsAndHashCode
    public static class IntegerCondition extends CaseCondition {
        private Literal value;

        public <T> T accept(Visitor<T> visitor) {
            return visitor.visit(this);
        }

        @Override
        public IntegerCondition copy() {
            return new IntegerCondition(value.copy());
        }
    }

    @EqualsAndHashCode
    @AllArgsConstructor
    @Data
    public static class Enumeration extends CaseCondition {
        private Literal start;
        private Literal stop;

        public Enumeration(Literal start) {
            this.start = this.stop = start;
        }

        public <T> T accept(Visitor<T> visitor) {
            return visitor.visit(this);
        }

        @Override
        public Enumeration copy() {
            Enumeration e = new Enumeration(start.copy(), stop != null ? stop.copy() : null);
            e.setRuleContext(getRuleContext());
            return e;
        }

        /*@Override public Enumeration clone() {
            Enumeration e = new Enumeration(start.clone());
            if (stop != null)
                e.stop = stop.clone();
            return e;
        }*/
    }
}

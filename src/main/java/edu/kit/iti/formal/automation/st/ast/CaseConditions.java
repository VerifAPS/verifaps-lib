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

import edu.kit.iti.formal.automation.ValueFactory;
import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * <p>Abstract CaseConditions class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public abstract class CaseConditions extends Top {
    public static class Range extends CaseConditions {
        private ScalarValue<? extends AnyInt, Integer> start, stop;

        public Range(ScalarValue<? extends AnyInt, Integer> start, ScalarValue<? extends AnyInt, Integer> stop) {
            this.start = start;
            this.stop = stop;
        }

        public Range(edu.kit.iti.formal.automation.st.ast.Range ast) {
            super();
        }


        public ScalarValue<? extends AnyInt, Integer> getStart() {
            return start;
        }

        public void setStart(ScalarValue<? extends AnyInt, Integer> start) {
            this.start = start;
        }

        public ScalarValue<? extends AnyInt, Integer> getStop() {
            return stop;
        }

        public void setStop(ScalarValue<? extends AnyInt, Integer> stop) {
            this.stop = stop;
        }


        public <T> T visit(Visitor<T> visitor) {
            return visitor.visit(this);
        }
    }

    public static class IntegerCondition extends CaseConditions {
        private ScalarValue<? extends AnyInt, Long> value;

        public IntegerCondition(ScalarValue<? extends AnyInt, Long> value) {
            this.value = value;
        }

        public ScalarValue<? extends AnyInt, Long> getValue() {
            return value;
        }

        public void setValue(ScalarValue<? extends AnyInt, Long> value) {
            this.value = value;
        }


        public <T> T visit(Visitor<T> visitor) {
            return visitor.visit(this);
        }
    }

    public static class Enumeration extends CaseConditions {
        private ScalarValue<EnumerateType, String> start;
        private ScalarValue<EnumerateType, String> stop;

        public Enumeration(ScalarValue<EnumerateType, String> start) {
            this.start = this.stop = start;
        }

        public Enumeration(String start, String stop) {
            this.start = ValueFactory.makeEnumeratedValue(start);
            this.stop = ValueFactory.makeEnumeratedValue(stop);
        }

        public Enumeration(String s) {
            this(ValueFactory.makeEnumeratedValue(s));
        }

        public ScalarValue<EnumerateType, String> getStart() {
            return start;
        }

        public void setStart(ScalarValue<EnumerateType, String> start) {
            this.start = start;
        }

        public ScalarValue<EnumerateType, String> getStop() {
            return stop;
        }

        public void setStop(ScalarValue<EnumerateType, String> stop) {
            this.stop = stop;
        }

        public <T> T visit(Visitor<T> visitor) {
            return visitor.visit(this);
        }
    }
}

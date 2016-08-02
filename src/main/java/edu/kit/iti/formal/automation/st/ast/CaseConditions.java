package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.ValueFactory;
import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.datatypes.AnyInt;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.visitors.Visitor;

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
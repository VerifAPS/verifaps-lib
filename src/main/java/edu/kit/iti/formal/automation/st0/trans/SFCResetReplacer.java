package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.st.ast.AssignmentStatement;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;
import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.datatypes.EnumerateType;
import edu.kit.iti.formal.automation.datatypes.values.Bits;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.st.util.AstCopyVisitor;

/**
 * Created by weigl on 28/10/14.
 */
public class SFCResetReplacer extends AstCopyVisitor {

    @Override
    public Object visit(AssignmentStatement assignmentStatement) {

        try {
            SymbolicReference sr = (SymbolicReference) assignmentStatement.getLocation();
            ScalarValue<AnyBit.Bool, Bits> value = (ScalarValue<AnyBit.Bool, Bits>) assignmentStatement.getExpression();

            if (sr.getIdentifier().endsWith("$SFCReset") && value.getValue().getRegister() > 0) {
                System.out.println(sr.getIdentifier());
                return new AssignmentStatement(
                        new SymbolicReference(sr.getIdentifier().replace("SFCReset", "_state")),
                        new ScalarValue<EnumerateType, String>(new EnumerateType(), "Init")
                );
            }

        } catch (ClassCastException e) {

        }
        return super.visit(assignmentStatement);
    }
}

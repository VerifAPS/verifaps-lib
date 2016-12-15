package edu.kit.iti.formal.automation.scope;

import edu.kit.iti.formal.automation.ValueFactory;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.datatypes.promotion.DefaultTypePromoter;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.st.ast.*;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigl on 26.11.16.
 */
public class FunctionResolverMUX implements FunctionResolver {
    @Override
    public FunctionDeclaration resolve(FunctionCall call, LocalScope scope) {
        if (call.getFunctionName().equals("MUX")) {

            List<Any> datatypes = call.getParameters().stream().map((expr) -> {
                try {
                    return expr.getExpression().dataType(scope);
                } catch (VariableNotDefinedException variableNotDefinedinScope) {
                    variableNotDefinedinScope.printStackTrace();
                } catch (TypeConformityException e) {
                    e.printStackTrace();
                }
                return null;
            }).collect(Collectors.toList());
            MUXFunctionDeclaration d = new MUXFunctionDeclaration(datatypes);

            return d;


        }
        return null;
    }

    public static class MUXFunctionDeclaration extends FunctionDeclaration {

        public MUXFunctionDeclaration(List<Any> call) {
            super();
            CaseStatement stmt = new CaseStatement();
            returnType = call.get(1);
            DefaultTypePromoter dtp = new DefaultTypePromoter();
            for (int i = 0; i < call.size(); i++) {
                localScope.add(new VariableDeclaration("a" + i,
                        VariableDeclaration.INPUT, call.get(i)));

                if (i > 0) {
                    stmt.addCase(createCase(i));
                    returnType = dtp.getPromotion(returnType,call.get(i));
                }
            }
            statements.add(stmt);
        }

        private static CaseStatement.Case createCase(int i) {
            CaseStatement.Case c = new CaseStatement.Case();
            c.addCondition(new CaseConditions.IntegerCondition(
                    ValueFactory.makeInt(i)));
            c.getStatements().add(new AssignmentStatement(new SymbolicReference("MUX"), new SymbolicReference("a" + i)));
            return c;
        }
    }
}

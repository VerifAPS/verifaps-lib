package edu.kit.iti.formal.automation.scope;

import edu.kit.iti.formal.automation.st.ast.FunctionCall;
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration;

/**
 * Created by weigl on 26.11.16.
 */
public class DefinedFunctionResolver implements FunctionResolver {
    @Override
    public FunctionDeclaration resolve(FunctionCall call, LocalScope scope) {
        return scope.getGlobalScope().getFunction(call.getFunctionName());
    }
}

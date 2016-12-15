package edu.kit.iti.formal.automation.scope;

import edu.kit.iti.formal.automation.st.ast.FunctionCall;
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration;

/**
 * Created by weigl on 26.11.16.
 */
public interface FunctionResolver {
    /**
     * Create or find function declaration that is suitable for the function call.
     *
     * For example, "MUX" function has a ellipsis argument (so not possible),
     * on call site a declaration is generated.
     * @param call
     * @param scope
     * @return
     */
    public FunctionDeclaration resolve(FunctionCall call, LocalScope scope);
}

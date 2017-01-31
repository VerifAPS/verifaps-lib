package edu.kit.iti.formal.automation.testtables.diagnostic;

import edu.kit.iti.formal.automation.st.ast.FunctionBlockDeclaration;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;

import java.util.function.Function;

/**
 * @author Alexander Weigl
 * @version 1 (22.01.17)
 */
public interface DiagnosticModuleBuilder extends Function<GeneralizedTestTable, FunctionBlockDeclaration> {
}

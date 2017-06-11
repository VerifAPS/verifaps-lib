package edu.kit.iti.formal.automation.exceptions;

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

import edu.kit.iti.formal.automation.st.ast.FunctionCall;
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration;

/**
 * FunctionUndefinedException is thrown if
 * a function is used but not in the list of toplevel elements.
 *
 * @author weigl
 * @since 27.11.16.
 */
public class FunctionUndefinedException extends IECException {
    private final FunctionCall functionCall;

    public FunctionUndefinedException(FunctionCall call) {
        this.functionCall = call;
    }

    /**
     * @return the function call that could not be resolved
     * @since 0.1.12
     */
    public FunctionCall getFunctionCall() {
        return functionCall;
    }
}

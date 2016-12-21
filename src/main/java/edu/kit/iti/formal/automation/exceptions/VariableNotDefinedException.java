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

import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.ast.SymbolicReference;

/**
 * Created by weigl on 24.11.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class VariableNotDefinedException extends IECException {
    private final SymbolicReference reference;
    private final LocalScope localScope;

    /**
     * <p>Constructor for VariableNotDefinedException.</p>
     *
     * @param variableDeclarations a {@link edu.kit.iti.formal.automation.scope.LocalScope} object.
     * @param reference a {@link edu.kit.iti.formal.automation.st.ast.SymbolicReference} object.
     */
    public VariableNotDefinedException(LocalScope variableDeclarations, SymbolicReference reference) {
        this.localScope = variableDeclarations;
        this.reference = reference;
    }

    /**
     * <p>Getter for the field <code>reference</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.SymbolicReference} object.
     */
    public SymbolicReference getReference() {
        return reference;
    }

    /**
     * <p>Getter for the field <code>localScope</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.scope.LocalScope} object.
     */
    public LocalScope getLocalScope() {
        return localScope;
    }

    /** {@inheritDoc} */
    @Override
    public String getMessage() {
        return "Variable: " + reference.getIdentifier() + " not defined in the given localScope " + localScope;
    }
}

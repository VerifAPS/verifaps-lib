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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.st.Identifiable;
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.visitors.Utils;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.NonNull;
import org.apache.commons.lang3.StringUtils;

import java.util.ArrayList;
import java.util.List;

/**
 * Created by weigl on 11.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
public class SymbolicReference extends Reference {
    @NonNull
    private IdentifierPlaceHolder identifier = new IdentifierPlaceHolder();
    private ExpressionList subscripts;
    private SymbolicReference sub;
    private Any dataType;

    /**
     * Number of times reference is dereferenced.
     */
    private int derefCount = 0;

    /**
     * <p>Constructor for SymbolicReference.</p>
     *
     * @param s   a {@link java.lang.String} object.
     * @param sub a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     */
    public SymbolicReference(String s, SymbolicReference sub) {
        if (s == null)
            throw new IllegalArgumentException();
        this.sub = sub;
        identifier.setIdentifier(s);
    }

    /**
     * <p>Constructor for SymbolicReference.</p>
     *
     * @param s a {@link java.lang.String} object.
     */
    public SymbolicReference(String s) {
        this(s, null);
    }

    /**
     * <p>Constructor for SymbolicReference.</p>
     *
     * @param symbolicReference a {@link edu.kit.iti.formal.automation.st.ast.SymbolicReference} object.
     */
    public SymbolicReference(SymbolicReference symbolicReference) {
        this.identifier = symbolicReference.identifier;
        this.subscripts = symbolicReference.getSubscripts();
        this.sub = symbolicReference.sub;
        this.derefCount = symbolicReference.derefCount;
        this.dataType = symbolicReference.dataType;
        if (this.identifier == null)
            throw new IllegalArgumentException();
    }

    /**
     * <p>Constructor for SymbolicReference.</p>
     */
    public SymbolicReference() {

    }

    public SymbolicReference(List<SymbolicReference> symbolicReferenceList) {
        this(symbolicReferenceList.get(0));
        sub = symbolicReferenceList.size() > 1
                ? new SymbolicReference(symbolicReferenceList.subList(1, symbolicReferenceList.size()))
                : null;
    }

    /**
     * <p>addSubscript.</p>
     *
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public void addSubscript(Expression ast) {
        if (subscripts == null)
            subscripts = new ExpressionList();
        subscripts.add(ast);
    }

    /**
     * <p>Getter for the field <code>identifier</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    @NonNull
    public String getIdentifier() {
        return identifier.getIdentifier();
    }

    /**
     * <p>Setter for the field <code>identifier</code>.</p>
     *
     * @param identifier a {@link java.lang.String} object.
     */
    public void setIdentifier(String identifier) {
        if (identifier == null)
            throw new IllegalArgumentException();
        this.identifier.setIdentifier(identifier);
    }

    public Identifiable getIdentifiedObject() {
        return identifier.getIdentifiedObject();
    }

    public void setIdentifiedObject(Identifiable identifiedObject) {
        identifier.setIdentifiedObject(identifiedObject);
    }

    public boolean hasSub() {
        return sub != null;
    }

    /**
     * @return The symbolic reference in a flat list format containing all its subreferences and starting with the
     * reference itself.
     */
    public List<SymbolicReference> asList() {
        List<SymbolicReference> list = new ArrayList<>();
        if (sub != null)
            list.addAll(sub.asList());
        list.add(0, this);
        return list;
    }

    public boolean isArrayAccess() {
        return subscripts != null;
    }

    /**
     * @return The local scope in which the reference is declared, or null if the scope cannot be determined.
     */
    public LocalScope getLocalScope() {
        Identifiable identifiedObject = getIdentifiedObject();
        if (identifiedObject instanceof VariableDeclaration)
            return ((VariableDeclaration) identifiedObject).getParent();
        else if (identifiedObject instanceof MethodDeclaration)
            return ((MethodDeclaration) identifiedObject).getParent().getLocalScope();
        return null;
    }

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Any dataType(LocalScope localScope)
            throws VariableNotDefinedException {
        return localScope.getVariable(this).getDataType();
    }

    @Override
    public SymbolicReference copy() {
        SymbolicReference sr = new SymbolicReference();
        sr.setRuleContext(getRuleContext());
        sr.identifier = identifier.copy();
        sr.subscripts = Utils.copyNull(subscripts);
        sr.sub = Utils.copyNull(sub);
        sr.derefCount = derefCount;
        sr.dataType = dataType;
        return sr;
    }

    @Override
    public String toString() {
        return getIdentifier()
                + StringUtils.repeat('^', derefCount)
                + (subscripts != null ? subscripts.toString() : "")
                + (sub == null ? "" : "." + sub.toString());
    }
}

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
import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 11.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class SymbolicReference extends Reference {
    private String identifier;
    private ExpressionList subscripts;
    private Reference sub;

    /**
     * <p>Constructor for SymbolicReference.</p>
     *
     * @param s   a {@link java.lang.String} object.
     * @param sub a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     */
    public SymbolicReference(String s, Reference sub) {
        if (s == null)
            throw new IllegalArgumentException();
        this.sub = sub;
        identifier = s;
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
        if (this.identifier == null)
            throw new IllegalArgumentException();
    }

    /**
     * <p>Constructor for SymbolicReference.</p>
     */
    public SymbolicReference() {

    }

    /**
     * <p>addSubscript.</p>
     *
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.Expression} object.
     */
    public void addSubscript(Expression ast) {
        subscripts.add(ast);
    }

    /**
     * <p>Getter for the field <code>identifier</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getIdentifier() {
        return identifier;
    }

    /**
     * <p>Setter for the field <code>identifier</code>.</p>
     *
     * @param identifier a {@link java.lang.String} object.
     */
    public void setIdentifier(String identifier) {
        if (identifier == null)
            throw new IllegalArgumentException();
        this.identifier = identifier;
    }

    /**
     * <p>Getter for the field <code>subscripts</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.ExpressionList} object.
     */
    public ExpressionList getSubscripts() {
        return subscripts;
    }

    /**
     * <p>Setter for the field <code>subscripts</code>.</p>
     *
     * @param subscripts a {@link edu.kit.iti.formal.automation.st.ast.ExpressionList} object.
     */
    public void setSubscripts(ExpressionList subscripts) {
        this.subscripts = subscripts;
    }

    /**
     * <p>Getter for the field <code>sub</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     */
    public Reference getSub() {
        return sub;
    }

    /**
     * <p>Setter for the field <code>sub</code>.</p>
     *
     * @param sub a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     */
    public void setSub(Reference sub) {
        this.sub = sub;
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean equals(Object o) {
        if (this == o)
            return true;
        if (!(o instanceof SymbolicReference))
            return false;

        SymbolicReference that = (SymbolicReference) o;

        if (!identifier.equals(that.identifier))
            return false;
        if (sub != null ? !sub.equals(that.sub) : that.sub != null)
            return false;
        if (subscripts != null ?
                !subscripts.equals(that.subscripts) :
                that.subscripts != null)
            return false;

        return true;
    }

    /**
     * {@inheritDoc}
     */
    @Override public int hashCode() {
        int result = identifier.hashCode();
        result = 31 * result + (subscripts != null ? subscripts.hashCode() : 0);
        result = 31 * result + (sub != null ? sub.hashCode() : 0);
        return result;
    }

    /**
     * <p>derefVar.</p>
     */
    public void derefVar() {
    }

    /**
     * <p>derefSubscript.</p>
     */
    public void derefSubscript() {

    }

    /**
     * {@inheritDoc}
     */
    @Override public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override public Any dataType(LocalScope localScope)
            throws VariableNotDefinedException {
        return localScope.getVariable(this).getDataType();
    }

    @Override public SymbolicReference clone() {
        SymbolicReference sr = new SymbolicReference();
        sr.identifier = identifier;
        sr.subscripts = subscripts.clone();
        sr.sub = sub.clone();
        return sr;
    }
}

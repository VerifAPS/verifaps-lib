package edu.kit.iti.formal.automation.st.util;

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

import edu.kit.iti.formal.automation.st.ast.AssignmentStatement;
import edu.kit.iti.formal.automation.visitors.Visitable;

import java.util.HashSet;
import java.util.Set;

/**
 * Created by weigl on 10/07/14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class UsageFinder extends AstVisitor {
    private Set<String> writtenReferences = new HashSet<>();
    private Set<String> readedReference = new HashSet<>();

    /** {@inheritDoc} */
    @Override
    public Object visit(AssignmentStatement assignmentStatement) {
        writtenReferences.add(assignmentStatement.getLocation().toString());
        assignmentStatement.getExpression().accept(this);
        return null;
    }

    /*@Override
    public Object accept(SymbolicReference symbolicReference) {
        readedReference.add(symbolicReference.getIdentifier());
        return null;
    }*/

    /**
     * <p>Getter for the field <code>writtenReferences</code>.</p>
     *
     * @return a {@link java.util.Set} object.
     */
    public Set<String> getWrittenReferences() {
        return writtenReferences;
    }

    /**
     * <p>Setter for the field <code>writtenReferences</code>.</p>
     *
     * @param writtenReferences a {@link java.util.Set} object.
     */
    public void setWrittenReferences(Set<String> writtenReferences) {
        this.writtenReferences = writtenReferences;
    }

    /**
     * <p>Getter for the field <code>readedReference</code>.</p>
     *
     * @return a {@link java.util.Set} object.
     */
    public Set<String> getReadedReference() {
        return readedReference;
    }

    /**
     * <p>Setter for the field <code>readedReference</code>.</p>
     *
     * @param readedReference a {@link java.util.Set} object.
     */
    public void setReadedReference(Set<String> readedReference) {
        this.readedReference = readedReference;
    }

    /**
     * <p>investigate.</p>
     *
     * @param visitable a {@link edu.kit.iti.formal.automation.visitors.Visitable} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.UsageFinder} object.
     */
    public static UsageFinder investigate(Visitable visitable) {
        UsageFinder waf = new UsageFinder();
        visitable.accept(waf);
        return waf;
    }
}

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
import edu.kit.iti.formal.automation.scope.Scope;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigl on 02.08.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class Location extends Expression {
    List<Reference> path = new ArrayList<>(5);

    /**
     * <p>Constructor for Location.</p>
     */
    public Location() {
    }

    /**
     * <p>Constructor for Location.</p>
     *
     * @param path a {@link java.util.List} object.
     */
    public Location(List<Reference> path) {
        this.path = path;
    }

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * <p>add.</p>
     *
     * @param ast a {@link edu.kit.iti.formal.automation.st.ast.Reference} object.
     */
    public void add(Reference ast) {
        path.add(ast);
    }

    /**
     * <p>lastDeref.</p>
     */
    public void lastDeref() {
        Deref deref = new Deref(path.get(path.size() - 1));
        path.remove(path.size() - 1);
        path.add(deref);
    }

    /**
     * <p>asIdentifier.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String asIdentifier() {
        return path.stream().map(a -> a.toString()).reduce("", (a, b) -> a + "." + b);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Any dataType(Scope localScope) {
        return null;//TODO
    }

    @Override
    public Location copy() {
        Location l = new Location(
                path.stream().map(Reference::copy)
                .collect(Collectors.toList()));
        l.setRuleContext(getRuleContext());
        return l;
    }
}

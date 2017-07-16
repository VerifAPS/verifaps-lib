package edu.kit.iti.formal.automation.datatypes;

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

import edu.kit.iti.formal.automation.st.Identifiable;

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public abstract class Any implements Identifiable {
    protected String name = "any";

    @Override
    public String getIdentifier() {
        return name;
    }

    /**
     * <p>Constructor for Any.</p>
     */
    protected Any() {
        name = getClass().getSimpleName().toUpperCase();
    }

    /**
     * <p>Constructor for Any.</p>
     *
     * @param name a {@link java.lang.String} object.
     */
    protected Any(String name) {
        this.name = name;
    }

    /**
     * <p>Setter for the field <code>name</code>.</p>
     *
     * @param name a {@link java.lang.String} object.
     */
    protected void setName(String name) {
        this.name = name;
    }

    /**
     * <p>Getter for the field <code>name</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getName() {
        return name;
    }

    /**
     * <p>repr.</p>
     *
     * @param obj a {@link java.lang.Object} object.
     * @return a {@link java.lang.String} object.
     */
    public abstract String repr(Object obj);

    /**
     * <p>accept.</p>
     *
     * @param visitor a {@link edu.kit.iti.formal.automation.datatypes.DataTypeVisitor} object.
     * @param <T> a T object.
     * @return a T object.
     */
    public abstract <T> T accept(DataTypeVisitor<T> visitor);
}

package edu.kit.iti.formal.automation.st;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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

import edu.kit.iti.formal.automation.st.ast.Copyable;
import lombok.Data;
import lombok.NoArgsConstructor;

/**
 * @param <T> an class which is identifiable
 * @author Alexander Weigl
 * @since 04.03.2017
 */
@Data
@NoArgsConstructor
public class IdentifierPlaceHolder<T extends Identifiable>
        implements Copyable<IdentifierPlaceHolder> {
    private String identifier;
    private T realObject;

    public IdentifierPlaceHolder(String identifier) {
        this.identifier = identifier;
    }

    public boolean isIdentified() {
        return getIdentifiedObject() != null;
    }

    public String getIdentifier() {
        if (realObject != null)
            return realObject.getIdentifier();
        return identifier;
    }

    public IdentifierPlaceHolder setIdentifier(String identifier) {
        if (realObject != null)
            return this;
        this.identifier = identifier;
        return this;
    }

    public T getIdentifiedObject() {
        return realObject;
    }

    public IdentifierPlaceHolder setIdentifiedObject(T realObject) {
        // TODO: assertion should be changed
        //assert identifier == null || realObject == null || realObject.getIdentifier().equals(identifier);
        this.realObject = realObject;
        if (realObject != null)
            identifier = realObject.getIdentifier();
        return this;
    }

    @Override
    public IdentifierPlaceHolder<T> copy() {
        IdentifierPlaceHolder<T> iph = new IdentifierPlaceHolder();
        iph.identifier = identifier;
        iph.realObject = realObject;
        return iph;
    }
}

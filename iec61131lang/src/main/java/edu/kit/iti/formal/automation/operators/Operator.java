package edu.kit.iti.formal.automation.operators;

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

import edu.kit.iti.formal.automation.datatypes.AnyDt;

/**
 * A Operator is an binary or unary operation associated with a special keyword.
 * <p>
 * In ST there are only binary or unary operators. No ternary operator is defined.
 * <p>
 * An operator has symbol and a list of expected types.
 *
 * @author Alexander Weigl
 * @version 1
 */
public interface Operator {
    /**
     * <p>symbol.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    String symbol();

    /**
     * <p>getExpectedDataTypes.</p>
     *
     * @return an array of {@link edu.kit.iti.formal.automation.datatypes.AnyDt} objects.
     */
    AnyDt[] getExpectedDataTypes();
}


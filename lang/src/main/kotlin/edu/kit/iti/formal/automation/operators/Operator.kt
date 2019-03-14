package edu.kit.iti.formal.automation.operators

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.AnyDt

/**
 * A Operator isType an binary or unary operation associated with a special keyword.
 *
 * In ST there are only binary or unary operators. No ternary operator isType defined.
 *
 * An operator has symbol and a list of expected types.
 *
 * @author Alexander Weigl
 * @version 1
 */
interface Operator {
    val expectedDataTypes: Array<AnyDt>
    val symbol: String
}


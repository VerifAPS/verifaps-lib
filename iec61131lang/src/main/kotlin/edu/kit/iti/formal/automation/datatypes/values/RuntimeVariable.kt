package edu.kit.iti.formal.automation.datatypes.values

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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.AnyDt

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
class RuntimeVariable {
    /**
     *
     * Getter for the field `name`.
     *
     * @return a [java.lang.String] object.
     */
    /**
     *
     * Setter for the field `name`.
     *
     * @param name a [java.lang.String] object.
     */
    var name: String? = null
    /**
     *
     * Getter for the field `value`.
     *
     * @return a [java.lang.Object] object.
     */
    /**
     *
     * Setter for the field `value`.
     *
     * @param value a [java.lang.Object] object.
     */
    var value: Any? = null
    /**
     *
     * Getter for the field `dataType`.
     *
     * @return a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     */
    /**
     *
     * Setter for the field `dataType`.
     *
     * @param dataType a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     */
    var dataType: AnyDt? = null

    /**
     *
     * Constructor for RuntimeVariable.
     *
     * @param name a [java.lang.String] object.
     */
    constructor(name: String) {
        this.name = name
    }

    /**
     *
     * Constructor for RuntimeVariable.
     *
     * @param name a [java.lang.String] object.
     * @param dataType a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     */
    constructor(name: String, dataType: AnyDt) {
        this.name = name
        this.dataType = dataType
    }

    /**
     *
     * Constructor for RuntimeVariable.
     *
     * @param name a [java.lang.String] object.
     * @param value a [java.lang.Object] object.
     * @param dataType a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     */
    constructor(name: String, value: Any, dataType: AnyDt) {
        this.name = name
        this.value = value
        this.dataType = dataType
    }
}

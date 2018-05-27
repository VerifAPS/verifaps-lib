package edu.kit.iti.formal.automation.datatypes

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

import edu.kit.iti.formal.automation.st.ast.ArrayTypeDeclaration
import edu.kit.iti.formal.automation.st.ast.Range

import java.util.ArrayList

/**
 * Created by weigl on 07/10/14.
 *
 * @author weigl
 * @version $Id: $Id
 */
class IECArray : AnyDt {
    /**
     *
     * Getter for the field `fieldType`.
     *
     * @return a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     */
    val fieldType: AnyDt?
    /**
     *
     * Getter for the field `ranges`.
     *
     * @return a [java.util.List] object.
     */
    /**
     *
     * Setter for the field `ranges`.
     *
     * @param ranges a [java.util.List] object.
     */
    var ranges: List<Range> = ArrayList()

    /**
     *
     * Constructor for IECArray.
     *
     * @param name a [java.lang.String] object.
     * @param fieldType a [edu.kit.iti.formal.automation.datatypes.AnyDt] object.
     * @param ranges a [java.util.List] object.
     */
    constructor(name: String, fieldType: AnyDt, ranges: List<Range>) {
        this.name = name
        this.fieldType = fieldType
        this.ranges = ranges
    }

    constructor(arrayTypeDeclaration: ArrayTypeDeclaration) {
        fieldType = arrayTypeDeclaration.baseType
        ranges = arrayTypeDeclaration.ranges
    }

    /** {@inheritDoc}  */
    override fun repr(obj: Any): String? {
        return null
    }


    /** {@inheritDoc}  */
    override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
        return visitor.visit(this)
    }
}

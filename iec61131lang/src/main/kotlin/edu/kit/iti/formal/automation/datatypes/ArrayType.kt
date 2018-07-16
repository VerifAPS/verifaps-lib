package edu.kit.iti.formal.automation.datatypes

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

import edu.kit.iti.formal.automation.st.ast.Range
import java.util.*

/**
 * Created by weigl on 07/10/14.
 *
 * @author weigl
 * @version $Id: $Id
 */
class ArrayType(name: String, val fieldType: AnyDt, var ranges: MutableList<Range> = ArrayList()) : AnyDt(name) {
    constructor(fieldType: AnyDt, ranges: List<Range>)
            : this("ARRAY OF ${fieldType.name}", fieldType, ranges.toMutableList())

    /*
    constructor(arrayTypeDeclaration: ArrayTypeDeclaration) {
        fieldType = arrayTypeDeclaration.baseType
        ranges = arrayTypeDeclaration.ranges
    }
    */

    override fun repr(obj: Any): String = TODO()
    override fun <T> accept(visitor: DataTypeVisitorNN<T>): T = visitor.visit(this)

    fun allIndices() =
            ranges.map { IntRange(it.startValue, it.stopValue) }
                    .fold(listOf(listOf())) { acc: List<List<Int>>, range: IntRange ->
                        acc.flatMap { l ->
                            range.map { r ->
                                l + r
                            }
                        }
                    }

    fun dimSize(d: Int): Int = ranges[d].stopValue
}

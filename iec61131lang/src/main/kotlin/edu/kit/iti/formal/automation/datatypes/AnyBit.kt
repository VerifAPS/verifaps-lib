package edu.kit.iti.formal.automation.datatypes

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%s
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

import edu.kit.iti.formal.automation.datatypes.values.Bits
import java.util.*

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
abstract class AnyBit(var bitLength: Int = 0) : AnyDt() {
    override fun <T> accept(visitor: DataTypeVisitor<T>): T = visitor.visit(this)

    override fun repr(obj: Any): String {
        if (obj is Bits) {
            if (obj.register > 0)
                return (javaClass.name.toUpperCase() + "#2#"
                        + java.lang.Long.toBinaryString(obj.register))
        }
        return ""
    }

    object BOOL : AnyBit(1) {
        override fun repr(obj: Any): String {
            if (obj is Bits) {
                if (obj.register > 0)
                    return "TRUE"
            }

            if (obj is Boolean) {
                if (obj)
                    return "TRUE"
            }
            return "FALSE"
        }

        override fun <T> accept(visitor: DataTypeVisitor<T>) = visitor.visit(this)
    }

    object BYTE : AnyBit(8) {
        override fun <T> accept(visitor: DataTypeVisitor<T>) = visitor.visit(this)
    }

    object WORD : AnyBit(16) {
        override fun <T> accept(visitor: DataTypeVisitor<T>) = visitor.visit(this)
    }

    object DWORD : AnyBit(32) {
        override fun <T> accept(visitor: DataTypeVisitor<T>) = visitor.visit(this)
    }

    object LWORD : AnyBit(64) {
        override fun <T> accept(visitor: DataTypeVisitor<T>) = visitor.visit(this)
    }

    companion object {
        val DATATYPES = Arrays.asList(AnyBit.BYTE,
                AnyBit.LWORD, AnyBit.WORD, AnyBit.DWORD, AnyBit.BOOL)
    }
}

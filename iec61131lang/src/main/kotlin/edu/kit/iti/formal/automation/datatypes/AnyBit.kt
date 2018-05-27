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

import edu.kit.iti.formal.automation.datatypes.values.Bits

import java.util.Arrays

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
abstract class AnyBit private constructor(bitLength: Int) : AnyDt() {


    /**
     *
     * Getter for the field `bitLength`.
     *
     * @return a int.
     */
    var bitLength: Int = 0
        protected set

    init {
        this.bitLength = bitLength
    }


    /**
     * {@inheritDoc}
     */
    override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
        return visitor.visit(this)
    }

    /**
     * {@inheritDoc}
     */
    override fun repr(obj: Any): String {
        if (obj is Bits) {
            if (obj.register > 0)
                return (javaClass.getName().toUpperCase() + "#2#"
                        + java.lang.Long.toBinaryString(obj.register))
        }
        return ""
    }

    class Bool : AnyBit(1) {

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

        override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
            return visitor.visit(this)
        }
    }

    class Byte : AnyBit(8) {

        override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
            return visitor.visit(this)
        }
    }

    class Word : AnyBit(16) {

        override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
            return visitor.visit(this)
        }
    }

    class DWord : AnyBit(32) {

        override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
            return visitor.visit(this)
        }
    }

    class LWord : AnyBit(64) {

        override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
            return visitor.visit(this)
        }
    }

    companion object {
        /**
         * Constant `BOOL`
         */
        val BOOL = Bool()
        /**
         * Constant `BYTE`
         */
        val BYTE = Byte()
        /**
         * Constant `WORD`
         */
        val WORD = Word()
        /**
         * Constant `DWORD`
         */
        val DWORD = DWord()
        /**
         * Constant `LWORD`
         */
        val LWORD = LWord()

        val DATATYPES = Arrays.asList(AnyBit.BYTE,
                AnyBit.LWORD, AnyBit.WORD, AnyBit.DWORD, AnyBit.BOOL)
    }
}

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

import java.util.ArrayList

/**
 * Created by weigl on 10.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
class EnumerateType : AnyDt {
    override var name: String? = null
        private set
    /**
     *
     * Getter for the field `allowedValues`.
     *
     * @return a [java.util.List] object.
     */
    /**
     *
     * Setter for the field `allowedValues`.
     *
     * @param allowedValues a [java.util.List] object.
     */
    var allowedValues: List<String> = ArrayList()
        set(allowedValues) {
            field = allowedValues
            bitlength = Math.ceil(Math.log(allowedValues.size.toDouble())).toInt()
        }
    /**
     *
     * Getter for the field `defValue`.
     *
     * @return a [java.lang.String] object.
     */
    /**
     *
     * Setter for the field `defValue`.
     *
     * @param defValue a [java.lang.String] object.
     */
    var defValue: String? = null
        set(defValue) {
            assert(isAllowedValue(defValue))
            field = defValue
        }
    private var bitlength: Int = 0

    /**
     *
     * Constructor for EnumerateType.
     */
    constructor() {
        //the unknown type
    }

    /**
     *
     * Constructor for EnumerateType.
     *
     * @param name a [java.lang.String] object.
     * @param allowedValues a [java.util.List] object.
     * @param defValue a [java.lang.String] object.
     */
    @JvmOverloads constructor(name: String, allowedValues: List<String>, defValue: String = allowedValues[0]) {
        this.name = name
        allowedValues = allowedValues
        defValue = defValue
    }

    /**
     *
     * Constructor for EnumerateType.
     *
     * @param prefix a [java.lang.String] object.
     */
    constructor(prefix: String) {
        this.name = prefix
    }

    /**
     *
     * Getter for the field `name`.
     *
     * @return a [java.lang.String] object.
     */
    override fun getName(): String? {
        return name
    }

    /** {@inheritDoc}  */
    public override fun setName(name: String) {
        this.name = name
    }

    /** {@inheritDoc}  */
    override fun repr(obj: Any): String {
        return if (name == null)
            obj.toString()
        else
            "$name#$obj"
    }


    /** {@inheritDoc}  */
    override fun <T> accept(visitor: DataTypeVisitor<T>): T? {
        return visitor.visit(this)
    }

    fun isAllowedValue(value: String): Boolean {
        return this.allowedValues.contains(value)
    }
}
/**
 *
 * Constructor for EnumerateType.
 *
 * @param name a [java.lang.String] object.
 * @param allowedValues a [java.util.List] object.
 */

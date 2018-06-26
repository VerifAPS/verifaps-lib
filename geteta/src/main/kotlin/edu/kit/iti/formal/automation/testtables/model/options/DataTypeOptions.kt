/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
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
 */
package edu.kit.iti.formal.automation.testtables.model.options


/**
 * Created by weigl on 16.12.16.
 */
class DataTypeOptions {

    private var widthInt = 16

    private var widthUInt = 16

    private var widthSInt = 8

    private var widthUSInt = 8

    private var widthLInt = 64

    private var widthULInt = 64

    private var widthDInt = 32

    private var widthUDInt = 32

    @Property("int")
    fun getWidthInt(): Int {
        return widthInt
    }

    fun setWidthInt(widthInt: Int): DataTypeOptions {
        this.widthInt = widthInt
        return this
    }

    @Property("uint")
    fun getWidthUInt(): Int {
        return widthUInt
    }

    fun setWidthUInt(widthUInt: Int): DataTypeOptions {
        this.widthUInt = widthUInt
        return this
    }

    @Property("sint")
    fun getWidthSInt(): Int {
        return widthSInt
    }

    fun setWidthSInt(widthSInt: Int): DataTypeOptions {
        this.widthSInt = widthSInt
        return this
    }

    @Property("usint")
    fun getWidthUSInt(): Int {
        return widthUSInt
    }

    fun setWidthUSInt(widthUSInt: Int): DataTypeOptions {
        this.widthUSInt = widthUSInt
        return this
    }

    @Property("lint")
    fun getWidthLInt(): Int {
        return widthLInt
    }

    fun setWidthLInt(widthLInt: Int): DataTypeOptions {
        this.widthLInt = widthLInt
        return this
    }

    @Property("ulint")
    fun getWidthULInt(): Int {
        return widthULInt
    }

    fun setWidthULInt(widthULInt: Int): DataTypeOptions {
        this.widthULInt = widthULInt
        return this
    }

    @Property("dint")
    fun getWidthDInt(): Int {
        return widthDInt
    }

    fun setWidthDInt(widthDInt: Int): DataTypeOptions {
        this.widthDInt = widthDInt
        return this
    }

    fun getWidthUDInt(): Int {
        return widthUDInt
    }

    @Property("udint")
    fun setWidthUDInt(widthUDInt: Int): DataTypeOptions {
        this.widthUDInt = widthUDInt
        return this
    }
}

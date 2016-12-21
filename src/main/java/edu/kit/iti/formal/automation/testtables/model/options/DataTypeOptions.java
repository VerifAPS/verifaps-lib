package edu.kit.iti.formal.automation.testtables.model.options;

/*-
 * #%L
 * geteta
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

/**
 * Created by weigl on 16.12.16.
 */
public class DataTypeOptions {

    @Property("int")
    private int widthInt = 16;

    @Property("uint")
    private int widthUInt = 16;

    @Property("sint")
    private int widthSInt = 8;

    @Property("usint")
    private int widthUSInt = 8;

    @Property("lint")
    private int widthLInt = 64;

    @Property("ulint")
    private int widthULInt = 64;

    @Property("dint")
    private int widthDInt = 32;

    @Property("udint")
    private int widthUDInt = 32;

    public int getWidthInt() {
        return widthInt;
    }

    public DataTypeOptions setWidthInt(int widthInt) {
        this.widthInt = widthInt;
        return this;
    }

    public int getWidthUInt() {
        return widthUInt;
    }

    public DataTypeOptions setWidthUInt(int widthUInt) {
        this.widthUInt = widthUInt;
        return this;
    }

    public int getWidthSInt() {
        return widthSInt;
    }

    public DataTypeOptions setWidthSInt(int widthSInt) {
        this.widthSInt = widthSInt;
        return this;
    }

    public int getWidthUSInt() {
        return widthUSInt;
    }

    public DataTypeOptions setWidthUSInt(int widthUSInt) {
        this.widthUSInt = widthUSInt;
        return this;
    }

    public int getWidthLInt() {
        return widthLInt;
    }

    public DataTypeOptions setWidthLInt(int widthLInt) {
        this.widthLInt = widthLInt;
        return this;
    }

    public int getWidthULInt() {
        return widthULInt;
    }

    public DataTypeOptions setWidthULInt(int widthULInt) {
        this.widthULInt = widthULInt;
        return this;
    }

    public int getWidthDInt() {
        return widthDInt;
    }

    public DataTypeOptions setWidthDInt(int widthDInt) {
        this.widthDInt = widthDInt;
        return this;
    }

    public int getWidthUDInt() {
        return widthUDInt;
    }

    public DataTypeOptions setWidthUDInt(int widthUDInt) {
        this.widthUDInt = widthUDInt;
        return this;
    }
}

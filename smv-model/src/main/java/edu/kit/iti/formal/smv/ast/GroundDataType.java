package edu.kit.iti.formal.smv.ast;

/*-
 * #%L
 * smv-model
 * %%
 * Copyright (C) 2017 Alexander Weigl
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

/*-
 * #%L
 * smv-model
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

public enum GroundDataType {
    SIGNED_WORD(true),
    UNSIGNED_WORD(true),
    INT, FLOAT, BOOLEAN, ENUM;

    public boolean hasWidth;

    GroundDataType() {
        this(false);
    }

    GroundDataType(boolean has_width) {
        hasWidth = has_width;
    }

    public Object parse(String value) {
        switch (this) {
            case FLOAT:
                return Float.parseFloat(value);
            case ENUM:
                return value;
            case INT:
            case SIGNED_WORD:
            case UNSIGNED_WORD:
                return Integer.parseInt(value);
            case BOOLEAN:
                return Boolean.parseBoolean(value);
        }
        return value;
    }

    public String format(Object value) {
        if (this == BOOLEAN) {
            boolean b = false;
            if (value instanceof Boolean) {
                b = (Boolean) value;
            }

            if (value instanceof Integer)
                b = ((Integer) value) != 0;

            if (value instanceof Long)
                b = ((Long) value) != 0;

            return Boolean.toString(b).toUpperCase();
        }
        return "" + value;
    }

}

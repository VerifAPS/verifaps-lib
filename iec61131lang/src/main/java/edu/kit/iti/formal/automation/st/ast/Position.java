package edu.kit.iti.formal.automation.st.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 - 2017 Alexander Weigl
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
 * @author Alexander Weigl
 * @version 1 (15.04.17)
 */
public class Position implements Cloneable {
    final int lineNumber;
    final int charInLine;

    public Position(int lineNumber, int charInLine) {
        this.lineNumber = lineNumber;
        this.charInLine = charInLine;
    }

    public Position() {
        this(-1, -1);
    }

    public int getLineNumber() {
        return lineNumber;
    }

    public int getCharInLine() {
        return charInLine;
    }

    @Override public Position clone() {
        return new Position(lineNumber, charInLine);
    }

    @Override public String toString() {
        return "@" + lineNumber + ":" + charInLine;
    }

    @Override public boolean equals(Object o) {
        if (this == o)
            return true;
        if (o == null || getClass() != o.getClass())
            return false;

        Position position = (Position) o;

        if (lineNumber != position.lineNumber)
            return false;
        return charInLine == position.charInLine;
    }

    @Override public int hashCode() {
        int result = lineNumber;
        result = 31 * result + charInLine;
        return result;
    }
}

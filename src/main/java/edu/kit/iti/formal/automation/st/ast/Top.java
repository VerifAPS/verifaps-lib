package edu.kit.iti.formal.automation.st.ast;

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
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */


import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.lang.reflect.AccessibleObject;
import java.lang.reflect.Field;
import java.util.HashMap;
import java.util.Map;

/**
 * <p>Abstract Top class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public abstract class Top implements Visitable {
    public static class Position {
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

        @Override
        public String toString() {
            return "@" + lineNumber + ":" + charInLine;
        }
    }

    private Position startPosition = new Position(),
            endPosition = new Position();


    /**
     * <p>Getter for the field <code>startPosition</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Top.Position} object.
     */
    public Position getStartPosition() {
        return startPosition;
    }

    /**
     * <p>Setter for the field <code>startPosition</code>.</p>
     *
     * @param start a {@link edu.kit.iti.formal.automation.st.ast.Top.Position} object.
     */
    public void setStartPosition(Position start) {
        this.startPosition = start;
    }

    /**
     * <p>Getter for the field <code>endPosition</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.Top.Position} object.
     */
    public Position getEndPosition() {
        return endPosition;
    }

    /**
     * <p>Setter for the field <code>endPosition</code>.</p>
     *
     * @param endPosition a {@link edu.kit.iti.formal.automation.st.ast.Top.Position} object.
     */
    public void setEndPosition(Position endPosition) {
        this.endPosition = endPosition;
    }

    private static void toString(Object o,
                                 Class<?> clazz,
                                 Map<String, Object> list) {
        Field f[] = clazz.getDeclaredFields();
        AccessibleObject.setAccessible(f, true);

        if (clazz.getSuperclass().getSuperclass() != null) {
            toString(o, clazz.getSuperclass(), list);
        }

        for (int i = 0; i < f.length; i++) {
            try {
                list.put(f[i].getName(), f[i].get(o));
            } catch (IllegalAccessException e) {
                e.printStackTrace();
            }
        }
    }

    /**
     * <p>getNodeName.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getNodeName() {
        return getClass().getName();
    }

    /**
     * <p>toString.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String toString() {
        StringBuilder sb = new StringBuilder();
        toString(0, sb);
        return sb.toString();
    }

    /**
     * <p>toString.</p>
     *
     * @param indent a int.
     * @param sb a {@link java.lang.StringBuilder} object.
     */
    protected void toString(int indent, StringBuilder sb) {
        Map<String, Object> fields = new HashMap<>();
        Top.toString(this, getClass(), fields);

        sb.append("(").append(getClass().getSimpleName()).append("\n");

        for (Map.Entry<String, Object> e : fields.entrySet()) {
            String tab = repeat(" ", indent + e.getKey().length());
            sb.append(tab).append(':').append(e.getKey()).append(' ');
            if (e.getValue() instanceof Top) {
                Top a = (Top) e.getValue();
                a.toString(indent + 3 + e.getKey().length(), sb);
            } else {
                sb.append(e.getValue());
            }
            sb.append("\n");
        }
        sb.setLength(sb.length() - 1);

        sb.append(")");

    }

    /**
     * <p>repeat.</p>
     *
     * @param str a {@link java.lang.String} object.
     * @param times a int.
     * @return a {@link java.lang.String} object.
     */
    public static String repeat(String str, int times) {
        StringBuilder sb = new StringBuilder();
        for (int i = 0; i < times; i++) {
            sb.append(str);
        }
        return sb.toString();
    }

    /** {@inheritDoc} */
    public abstract <T> T visit(Visitor<T> visitor);
}

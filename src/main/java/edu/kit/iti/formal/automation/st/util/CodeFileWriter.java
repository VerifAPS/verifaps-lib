package edu.kit.iti.formal.automation.st.util;

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

import java.io.IOException;
import java.io.Writer;
import java.util.Stack;

/**
 * <p>CodeFileWriter class.</p>
 *
 * @author weigla (15.06.2014)
 */
public class CodeFileWriter {
    private Writer fw;

    private String ident = "    ";
    private int identDepth = 0;
    private int lastSeperatorInsertPosition;
    private Stack<Boolean> lastIsDiv = new Stack<>();


    /**
     * <p>Constructor for CodeFileWriter.</p>
     *
     * @param fw a {@link java.io.Writer} object.
     */
    public CodeFileWriter(Writer fw) {
        this.fw = fw;
    }


    /**
     * <p>appendIdent.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeFileWriter} object.
     * @throws java.io.IOException if any.
     */
    public CodeFileWriter appendIdent() throws IOException {
        for (int i = 0; i < identDepth; i++) {
            fw.write(ident);
        }
        return this;
    }

    /**
     * <p>increaseIdent.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeFileWriter} object.
     */
    public CodeFileWriter increaseIdent() {
        identDepth++;
        return this;
    }

    /**
     * <p>decreaseIdent.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeFileWriter} object.
     */
    public CodeFileWriter decreaseIdent() {
        identDepth--;
        return this;
    }

    /**
     * <p>nl.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeFileWriter} object.
     * @throws java.io.IOException if any.
     */
    public CodeFileWriter nl() throws IOException {
        fw.write("\n");
        appendIdent();
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param obj a {@link java.lang.Object} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeFileWriter} object.
     * @throws java.io.IOException if any.
     */
    public CodeFileWriter append(Object obj) throws IOException {
        fw.write(obj.toString());
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param obj a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeFileWriter} object.
     * @throws java.io.IOException if any.
     */
    public CodeFileWriter append(String obj) throws IOException {
        fw.write(obj);
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param f a float.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeFileWriter} object.
     * @throws java.io.IOException if any.
     */
    public CodeFileWriter append(float f) throws IOException {
        fw.write(String.valueOf(f));
        return this;
    }


    /**
     * <p>append.</p>
     *
     * @param d a double.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeFileWriter} object.
     * @throws java.io.IOException if any.
     */
    public CodeFileWriter append(double d) throws IOException {
        fw.write(String.valueOf(d));
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param str an array of char.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeFileWriter} object.
     * @throws java.io.IOException if any.
     */
    public CodeFileWriter append(char[] str) throws IOException {
        fw.write(str);
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param str an array of char.
     * @param offset a int.
     * @param len a int.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeFileWriter} object.
     * @throws java.io.IOException if any.
     */
    public CodeFileWriter append(char[] str, int offset, int len) throws IOException {
        fw.write(str, offset, len);
        return this;
    }
}

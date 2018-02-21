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

import java.io.Serializable;
import java.util.Arrays;

/**
 * <p>CodeWriter class.</p>
 *
 * @author weigla (15.06.2014)
 * @version 1
 */
public class CodeWriter implements Serializable, CharSequence {
    protected StringBuilder sb = new StringBuilder();

    private boolean uppercaseKeywords = true;
    private String ident = "    ";
    private int identDepth = 0;

    /**
     * <p>appendf.</p>
     *
     * @param fmt  a {@link java.lang.String} object.
     * @param args a {@link java.lang.Object} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter appendf(String fmt, Object... args) {
        return append(String.format(fmt, args));
    }

    /**
     * <p>appendIdent.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter appendIdent() {
        for (int i = 0; i < identDepth; i++) {
            sb.append(ident);
        }
        return this;
    }

    /**
     * <p>increaseIndent.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter increaseIndent() {
        identDepth++;
        return this;
    }

    /**
     * <p>decreaseIndent.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter decreaseIndent() {
        identDepth = Math.max(identDepth - 1, 0);
        return this;
    }

    /**
     * <p>keyword.</p>
     *
     * @param keyword a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter keyword(String keyword) {
        return append(uppercaseKeywords ? keyword.toUpperCase() : keyword.toLowerCase());
    }

    /**
     * <p>nl.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter nl() {
        sb.append("\n");
        appendIdent();
        return this;
    }

    public CodeWriter append(Object... args) {
        Arrays.stream(args).forEach(this::append);
        return this;
    }

    public CodeWriter append(String fmt, Object... args) {
        return append(String.format(fmt, args));
    }


    /**
     * <p>append.</p>
     *
     * @param obj a {@link java.lang.Object} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(Object obj) {
        sb.append(obj);
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param f a float.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(float f) {
        sb.append(f);
        return this;
    }

    /**
     * <p>insert.</p>
     *
     * @param offset a int.
     * @param b      a boolean.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int offset, boolean b) {
        sb.insert(offset, b);
        return this;
    }

    /**
     * <p>lastIndexOf.</p>
     *
     * @param str       a {@link java.lang.String} object.
     * @param fromIndex a int.
     * @return a int.
     */
    public int lastIndexOf(String str, int fromIndex) {
        return sb.lastIndexOf(str, fromIndex);
    }

    /**
     * {@inheritDoc}
     */
    public char charAt(int index) {
        return sb.charAt(index);

    }

    /**
     * <p>codePointCount.</p>
     *
     * @param beginIndex a int.
     * @param endIndex   a int.
     * @return a int.
     */
    public int codePointCount(int beginIndex, int endIndex) {
        return sb.codePointCount(beginIndex, endIndex);

    }

    /**
     * <p>insert.</p>
     *
     * @param offset a int.
     * @param c      a char.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int offset, char c) {
        sb.insert(offset, c);
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param d a double.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(double d) {
        sb.append(d);
        return this;
    }

    /**
     * <p>insert.</p>
     *
     * @param dstOffset a int.
     * @param s         a {@link java.lang.CharSequence} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int dstOffset, CharSequence s) {
        sb.insert(dstOffset, s);
        return this;
    }

    /**
     * <p>offsetByCodePoints.</p>
     *
     * @param index           a int.
     * @param codePointOffset a int.
     * @return a int.
     */
    public int offsetByCodePoints(int index, int codePointOffset) {
        return sb.offsetByCodePoints(index, codePointOffset);
    }

    /**
     * <p>insert.</p>
     *
     * @param offset a int.
     * @param l      a long.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int offset, long l) {
        sb.insert(offset, l);
        return this;
    }

    /**
     * <p>insert.</p>
     *
     * @param offset a int.
     * @param i      a int.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int offset, int i) {
        sb.insert(offset, i);
        return this;
    }

    /**
     * <p>setCharAt.</p>
     *
     * @param index a int.
     * @param ch    a char.
     */
    public void setCharAt(int index, char ch) {
        sb.setCharAt(index, ch);

    }

    /**
     * <p>lastIndexOf.</p>
     *
     * @param str a {@link java.lang.String} object.
     * @return a int.
     */
    public int lastIndexOf(String str) {
        return sb.lastIndexOf(str);
    }

    /**
     * <p>ensureCapacity.</p>
     *
     * @param minimumCapacity a int.
     */
    public void ensureCapacity(int minimumCapacity) {
        sb.ensureCapacity(minimumCapacity);
    }

    /**
     * <p>substring.</p>
     *
     * @param start a int.
     * @return a {@link java.lang.String} object.
     */
    public String substring(int start) {
        return sb.substring(start);

    }

    /**
     * <p>append.</p>
     *
     * @param str an array of char.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(char[] str) {
        sb.append(str);
        return this;
    }

    /**
     * <p>codePointAt.</p>
     *
     * @param index a int.
     * @return a int.
     */
    public int codePointAt(int index) {
        return sb.codePointAt(index);
    }

    /**
     * <p>indexOf.</p>
     *
     * @param str       a {@link java.lang.String} object.
     * @param fromIndex a int.
     * @return a int.
     */
    public int indexOf(String str, int fromIndex) {
        return sb.indexOf(str, fromIndex);
    }

    /**
     * <p>append.</p>
     *
     * @param s     a {@link java.lang.CharSequence} object.
     * @param start a int.
     * @param end   a int.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(CharSequence s, int start, int end) {
        sb.append(s, start, end);
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param str    an array of char.
     * @param offset a int.
     * @param len    a int.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(char[] str, int offset, int len) {
        sb.append(str, offset, len);
        return this;
    }

    /**
     * <p>codePointBefore.</p>
     *
     * @param index a int.
     * @return a int.
     */
    public int codePointBefore(int index) {
        return sb.codePointBefore(index);
    }

    /**
     * <p>insert.</p>
     *
     * @param offset a int.
     * @param f      a float.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int offset, float f) {
        sb.insert(offset, f);
        return this;
    }

    /**
     * <p>substring.</p>
     *
     * @param start a int.
     * @param end   a int.
     * @return a {@link java.lang.String} object.
     */
    public String substring(int start, int end) {
        return sb.substring(start, end);
    }

    /**
     * <p>length.</p>
     *
     * @return a int.
     */
    public int length() {
        return sb.length();
    }

    /**
     * <p>append.</p>
     *
     * @param sb a {@link java.lang.StringBuffer} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(StringBuffer sb) {
        this.sb.append(sb);
        return this;
    }

    /**
     * <p>reverse.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter reverse() {
        sb.reverse();
        return this;
    }

    /**
     * <p>indexOf.</p>
     *
     * @param str a {@link java.lang.String} object.
     * @return a int.
     */
    public int indexOf(String str) {
        return sb.indexOf(str);
    }

    /**
     * <p>insert.</p>
     *
     * @param offset a int.
     * @param d      a double.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int offset, double d) {
        sb.insert(offset, d);
        return this;
    }

    /**
     * <p>trimToSize.</p>
     */
    public void trimToSize() {
        sb.trimToSize();
    }

    /**
     * <p>setLength.</p>
     *
     * @param newLength a int.
     */
    public void setLength(int newLength) {
        sb.setLength(newLength);
    }

    /**
     * <p>capacity.</p>
     *
     * @return a int.
     */
    public int capacity() {
        return sb.capacity();
    }

    /**
     * <p>insert.</p>
     *
     * @param offset a int.
     * @param str    an array of char.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int offset, char[] str) {
        sb.insert(offset, str);
        return this;
    }

    /**
     * <p>insert.</p>
     *
     * @param offset a int.
     * @param str    a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int offset, String str) {
        sb.insert(offset, str);
        return this;
    }

    /**
     * <p>appendCodePoint.</p>
     *
     * @param codePoint a int.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter appendCodePoint(int codePoint) {
        sb.appendCodePoint(codePoint);
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param c a char.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(char c) {
        sb.append(c);
        return this;
    }

    /**
     * {@inheritDoc}
     */
    public CharSequence subSequence(int start, int end) {
        return sb.subSequence(start, end);
    }

    /**
     * <p>delete.</p>
     *
     * @param start a int.
     * @param end   a int.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter delete(int start, int end) {
        sb.delete(start, end);
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param lng a long.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(long lng) {
        sb.append(lng);
        return this;
    }

    /**
     * <p>insert.</p>
     *
     * @param dstOffset a int.
     * @param s         a {@link java.lang.CharSequence} object.
     * @param start     a int.
     * @param end       a int.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int dstOffset, CharSequence s, int start, int end) {
        sb.insert(dstOffset, s, start, end);
        return this;
    }

    /**
     * <p>insert.</p>
     *
     * @param index  a int.
     * @param str    an array of char.
     * @param offset a int.
     * @param len    a int.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int index, char[] str, int offset, int len) {
        sb.insert(index, str, offset, len);
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param i a int.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(int i) {
        sb.append(i);
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param s a {@link java.lang.CharSequence} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(CharSequence s) {
        sb.append(s);
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param b a boolean.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(boolean b) {
        sb.append(b);
        return this;
    }

    /**
     * <p>insert.</p>
     *
     * @param offset a int.
     * @param obj    a {@link java.lang.Object} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter insert(int offset, Object obj) {
        sb.insert(offset, obj);
        return this;
    }

    /**
     * <p>append.</p>
     *
     * @param str a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter append(String str) {
        sb.append(str);
        return this;
    }

    /**
     * <p>deleteCharAt.</p>
     *
     * @param index a int.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter deleteCharAt(int index) {
        sb.deleteCharAt(index);
        return this;
    }

    /**
     * <p>getChars.</p>
     *
     * @param srcBegin a int.
     * @param srcEnd   a int.
     * @param dst      an array of char.
     * @param dstBegin a int.
     */
    public void getChars(int srcBegin, int srcEnd, char[] dst, int dstBegin) {
        sb.getChars(srcBegin, srcEnd, dst, dstBegin);
    }

    /**
     * <p>replace.</p>
     *
     * @param start a int.
     * @param end   a int.
     * @param str   a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter replace(int start, int end, String str) {
        sb.replace(start, end, str);
        return this;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String toString() {
        return sb.toString();
    }

    /**
     * <p>deleteLast.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter deleteLast() {
        return deleteLast(1);
    }

    /**
     * <p>deleteLast.</p>
     *
     * @param i a int.
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter deleteLast(int i) {
        sb.setLength(sb.length() - i);
        return this;
    }

    /**
     * <p>atLineStart.</p>
     *
     * @return a boolean.
     */
    public boolean atLineStart() {
        return sb.length() - 1 == sb.lastIndexOf("\n");
    }

    /**
     * no terminal sign printed
     *
     * @return a boolean.
     */
    public boolean isFreshLine() {
        int pos = sb.lastIndexOf("\n");
        if (pos != -1) {
            for (; pos < sb.length(); pos++) {
                if (!Character.isWhitespace(sb.charAt(pos)))
                    return false;
            }
            return true;
        } else {
            return sb.length() == 0;
        }
    }

    /**
     * <p>atWhitespace.</p>
     *
     * @return a boolean.
     */
    public boolean atWhitespace() {
        return Character.isWhitespace(sb.charAt(sb.length() - 1));
    }

    /**
     * <p>hardDecreaseIndent.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.CodeWriter} object.
     */
    public CodeWriter hardDecreaseIndent() {
        decreaseIndent();
        // remove '\n '
        int pos = sb.lastIndexOf("\n");
        sb.delete(pos, sb.length() - 1);
        return nl();
    }

}

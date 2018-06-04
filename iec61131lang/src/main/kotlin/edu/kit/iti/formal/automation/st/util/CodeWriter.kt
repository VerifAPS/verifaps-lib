package edu.kit.iti.formal.automation.st.util

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

import java.io.Serializable
import java.util.Arrays
import java.util.function.Consumer

/**
 *
 * CodeWriter class.
 *
 * @author weigla (15.06.2014)
 * @version 1
 */
open class CodeWriter : Serializable, CharSequence {
    protected var sb = StringBuilder()

    override val length: Int = sb.length
    override fun get(index: Int): Char = sb.get(index)

    private val uppercaseKeywords = true
    private val ident = "    "
    private var identDepth = 0

    /**
     * no terminal sign printed
     *
     * @return a boolean.
     */
    val isFreshLine: Boolean
        get() {
            var pos = sb.lastIndexOf("\n")
            if (pos != -1) {
                while (pos < sb.length) {
                    if (!Character.isWhitespace(sb[pos]))
                        return false
                    pos++
                }
                return true
            } else {
                return sb.length == 0
            }
        }

    /**
     *
     * appendf.
     *
     * @param fmt  a [java.lang.String] object.
     * @param args a [java.lang.Object] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun appendf(fmt: String, vararg args: Any): CodeWriter {
        return append(String.format(fmt, *args))
    }

    /**
     *
     * appendIdent.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun appendIdent(): CodeWriter {
        for (i in 0 until identDepth) {
            sb.append(ident)
        }
        return this
    }

    /**
     *
     * increaseIndent.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun increaseIndent(): CodeWriter {
        identDepth++
        return this
    }

    /**
     *
     * decreaseIndent.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun decreaseIndent(): CodeWriter {
        identDepth = Math.max(identDepth - 1, 0)
        return this
    }

    /**
     *
     * keyword.
     *
     * @param keyword a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    open fun keyword(keyword: String): CodeWriter {
        return append(if (uppercaseKeywords) keyword.toUpperCase() else keyword.toLowerCase())
    }

    /**
     *
     * nl.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun nl(): CodeWriter {
        sb.append("\n")
        appendIdent()
        return this
    }

    fun append(vararg args: Any): CodeWriter {
        Arrays.stream(args).forEach(Consumer<Any> { this.append(it) })
        return this
    }

    fun append(fmt: String, vararg args: Any): CodeWriter {
        return append(String.format(fmt, *args))
    }


    /**
     *
     * append.
     *
     * @param obj a [java.lang.Object] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(obj: Any): CodeWriter {
        sb.append(obj)
        return this
    }

    /**
     *
     * append.
     *
     * @param f a float.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(f: Float): CodeWriter {
        sb.append(f)
        return this
    }

    /**
     *
     * insert.
     *
     * @param offset a int.
     * @param b      a boolean.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(offset: Int, b: Boolean): CodeWriter {
        sb.insert(offset, b)
        return this
    }

    /**
     *
     * lastIndexOf.
     *
     * @param str       a [java.lang.String] object.
     * @param fromIndex a int.
     * @return a int.
     */
    fun lastIndexOf(str: String, fromIndex: Int): Int {
        return sb.lastIndexOf(str, fromIndex)
    }

    /**
     *
     * codePointCount.
     *
     * @param beginIndex a int.
     * @param endIndex   a int.
     * @return a int.
     */
    fun codePointCount(beginIndex: Int, endIndex: Int): Int {
        return sb.codePointCount(beginIndex, endIndex)

    }

    /**
     *
     * insert.
     *
     * @param offset a int.
     * @param c      a char.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(offset: Int, c: Char): CodeWriter {
        sb.insert(offset, c)
        return this
    }

    /**
     *
     * append.
     *
     * @param d a double.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(d: Double): CodeWriter {
        sb.append(d)
        return this
    }

    /**
     *
     * insert.
     *
     * @param dstOffset a int.
     * @param s         a [java.lang.CharSequence] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(dstOffset: Int, s: CharSequence): CodeWriter {
        sb.insert(dstOffset, s)
        return this
    }

    /**
     *
     * offsetByCodePoints.
     *
     * @param index           a int.
     * @param codePointOffset a int.
     * @return a int.
     */
    fun offsetByCodePoints(index: Int, codePointOffset: Int): Int {
        return sb.offsetByCodePoints(index, codePointOffset)
    }

    /**
     *
     * insert.
     *
     * @param offset a int.
     * @param l      a long.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(offset: Int, l: Long): CodeWriter {
        sb.insert(offset, l)
        return this
    }

    /**
     *
     * insert.
     *
     * @param offset a int.
     * @param i      a int.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(offset: Int, i: Int): CodeWriter {
        sb.insert(offset, i)
        return this
    }

    /**
     *
     * setCharAt.
     *
     * @param index a int.
     * @param ch    a char.
     */
    fun setCharAt(index: Int, ch: Char) {
        sb.setCharAt(index, ch)

    }

    /**
     *
     * lastIndexOf.
     *
     * @param str a [java.lang.String] object.
     * @return a int.
     */
    fun lastIndexOf(str: String): Int {
        return sb.lastIndexOf(str)
    }

    /**
     *
     * ensureCapacity.
     *
     * @param minimumCapacity a int.
     */
    fun ensureCapacity(minimumCapacity: Int) {
        sb.ensureCapacity(minimumCapacity)
    }

    /**
     *
     * substring.
     *
     * @param start a int.
     * @return a [java.lang.String] object.
     */
    fun substring(start: Int): String {
        return sb.substring(start)

    }

    /**
     *
     * append.
     *
     * @param str an array of char.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(str: CharArray): CodeWriter {
        sb.append(str)
        return this
    }

    /**
     *
     * codePointAt.
     *
     * @param index a int.
     * @return a int.
     */
    fun codePointAt(index: Int): Int {
        return sb.codePointAt(index)
    }

    /**
     *
     * indexOf.
     *
     * @param str       a [java.lang.String] object.
     * @param fromIndex a int.
     * @return a int.
     */
    fun indexOf(str: String, fromIndex: Int): Int {
        return sb.indexOf(str, fromIndex)
    }

    /**
     *
     * append.
     *
     * @param s     a [java.lang.CharSequence] object.
     * @param start a int.
     * @param end   a int.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(s: CharSequence, start: Int, end: Int): CodeWriter {
        sb.append(s, start, end)
        return this
    }

    /**
     *
     * append.
     *
     * @param str    an array of char.
     * @param offset a int.
     * @param len    a int.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(str: CharArray, offset: Int, len: Int): CodeWriter {
        sb.append(str, offset, len)
        return this
    }

    /**
     *
     * codePointBefore.
     *
     * @param index a int.
     * @return a int.
     */
    fun codePointBefore(index: Int): Int {
        return sb.codePointBefore(index)
    }

    /**
     *
     * insert.
     *
     * @param offset a int.
     * @param f      a float.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(offset: Int, f: Float): CodeWriter {
        sb.insert(offset, f)
        return this
    }

    /**
     *
     * substring.
     *
     * @param start a int.
     * @param end   a int.
     * @return a [java.lang.String] object.
     */
    fun substring(start: Int, end: Int): String {
        return sb.substring(start, end)
    }


    /**
     *
     * append.
     *
     * @param sb a [java.lang.StringBuffer] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(sb: StringBuffer): CodeWriter {
        this.sb.append(sb)
        return this
    }

    /**
     *
     * reverse.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun reverse(): CodeWriter {
        sb.reverse()
        return this
    }

    /**
     *
     * indexOf.
     *
     * @param str a [java.lang.String] object.
     * @return a int.
     */
    fun indexOf(str: String): Int {
        return sb.indexOf(str)
    }

    /**
     *
     * insert.
     *
     * @param offset a int.
     * @param d      a double.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(offset: Int, d: Double): CodeWriter {
        sb.insert(offset, d)
        return this
    }

    /**
     *
     * trimToSize.
     */
    fun trimToSize() {
        sb.trimToSize()
    }

    /**
     *
     * setLength.
     *
     * @param newLength a int.
     */
    fun setLength(newLength: Int) {
        sb.setLength(newLength)
    }

    /**
     *
     * capacity.
     *
     * @return a int.
     */
    fun capacity(): Int {
        return sb.capacity()
    }

    /**
     *
     * insert.
     *
     * @param offset a int.
     * @param str    an array of char.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(offset: Int, str: CharArray): CodeWriter {
        sb.insert(offset, str)
        return this
    }

    /**
     *
     * insert.
     *
     * @param offset a int.
     * @param str    a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(offset: Int, str: String): CodeWriter {
        sb.insert(offset, str)
        return this
    }

    /**
     *
     * appendCodePoint.
     *
     * @param codePoint a int.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun appendCodePoint(codePoint: Int): CodeWriter {
        sb.appendCodePoint(codePoint)
        return this
    }

    /**
     *
     * append.
     *
     * @param c a char.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(c: Char): CodeWriter {
        sb.append(c)
        return this
    }

    /**
     * {@inheritDoc}
     */
    override fun subSequence(start: Int, end: Int): CharSequence {
        return sb.subSequence(start, end)
    }

    /**
     *
     * delete.
     *
     * @param start a int.
     * @param end   a int.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun delete(start: Int, end: Int): CodeWriter {
        sb.delete(start, end)
        return this
    }

    /**
     *
     * append.
     *
     * @param lng a long.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(lng: Long): CodeWriter {
        sb.append(lng)
        return this
    }

    /**
     *
     * insert.
     *
     * @param dstOffset a int.
     * @param s         a [java.lang.CharSequence] object.
     * @param start     a int.
     * @param end       a int.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(dstOffset: Int, s: CharSequence, start: Int, end: Int): CodeWriter {
        sb.insert(dstOffset, s, start, end)
        return this
    }

    /**
     *
     * insert.
     *
     * @param index  a int.
     * @param str    an array of char.
     * @param offset a int.
     * @param len    a int.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(index: Int, str: CharArray, offset: Int, len: Int): CodeWriter {
        sb.insert(index, str, offset, len)
        return this
    }

    /**
     *
     * append.
     *
     * @param i a int.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(i: Int): CodeWriter {
        sb.append(i)
        return this
    }

    /**
     *
     * append.
     *
     * @param s a [java.lang.CharSequence] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(s: CharSequence): CodeWriter {
        sb.append(s)
        return this
    }

    /**
     *
     * append.
     *
     * @param b a boolean.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(b: Boolean): CodeWriter {
        sb.append(b)
        return this
    }

    /**
     *
     * insert.
     *
     * @param offset a int.
     * @param obj    a [java.lang.Object] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun insert(offset: Int, obj: Any): CodeWriter {
        sb.insert(offset, obj)
        return this
    }

    /**
     *
     * append.
     *
     * @param str a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun append(str: String): CodeWriter {
        sb.append(str)
        return this
    }

    /**
     *
     * deleteCharAt.
     *
     * @param index a int.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun deleteCharAt(index: Int): CodeWriter {
        sb.deleteCharAt(index)
        return this
    }

    /**
     *
     * getChars.
     *
     * @param srcBegin a int.
     * @param srcEnd   a int.
     * @param dst      an array of char.
     * @param dstBegin a int.
     */
    fun getChars(srcBegin: Int, srcEnd: Int, dst: CharArray, dstBegin: Int) {
        sb.getChars(srcBegin, srcEnd, dst, dstBegin)
    }

    /**
     *
     * replace.
     *
     * @param start a int.
     * @param end   a int.
     * @param str   a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun replace(start: Int, end: Int, str: String): CodeWriter {
        sb.replace(start, end, str)
        return this
    }

    /**
     * {@inheritDoc}
     */
    override fun toString(): String {
        return sb.toString()
    }

    /**
     *
     * deleteLast.
     *
     * @param i a int.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    @JvmOverloads
    fun deleteLast(i: Int = 1): CodeWriter {
        sb.setLength(sb.length - i)
        return this
    }

    /**
     *
     * atLineStart.
     *
     * @return a boolean.
     */
    fun atLineStart(): Boolean {
        return sb.length - 1 == sb.lastIndexOf("\n")
    }

    /**
     *
     * atWhitespace.
     *
     * @return a boolean.
     */
    fun atWhitespace(): Boolean {
        return Character.isWhitespace(sb[sb.length - 1])
    }

    /**
     *
     * hardDecreaseIndent.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
     */
    fun hardDecreaseIndent(): CodeWriter {
        decreaseIndent()
        // remove '\n '
        val pos = sb.lastIndexOf("\n")
        sb.delete(pos, sb.length - 1)
        return nl()
    }

}
/**
 *
 * deleteLast.
 *
 * @return a [edu.kit.iti.formal.automation.st.util.CodeWriter] object.
 */

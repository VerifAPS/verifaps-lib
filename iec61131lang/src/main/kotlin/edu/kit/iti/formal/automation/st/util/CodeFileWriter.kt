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

import java.io.IOException
import java.io.Writer
import java.util.Stack

/**
 *
 * CodeFileWriter class.
 *
 * @author weigla (15.06.2014)
 */
class CodeFileWriter
/**
 *
 * Constructor for CodeFileWriter.
 *
 * @param fw a [java.io.Writer] object.
 */
(private val fw: Writer) {

    private val ident = "    "
    private var identDepth = 0
    private val lastSeperatorInsertPosition: Int = 0
    private val lastIsDiv = Stack<Boolean>()


    /**
     *
     * appendIdent.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.CodeFileWriter] object.
     * @throws java.io.IOException if any.
     */
    @Throws(IOException::class)
    fun appendIdent(): CodeFileWriter {
        for (i in 0 until identDepth) {
            fw.write(ident)
        }
        return this
    }

    /**
     *
     * increaseIdent.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.CodeFileWriter] object.
     */
    fun increaseIdent(): CodeFileWriter {
        identDepth++
        return this
    }

    /**
     *
     * decreaseIdent.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.CodeFileWriter] object.
     */
    fun decreaseIdent(): CodeFileWriter {
        identDepth--
        return this
    }

    /**
     *
     * nl.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.CodeFileWriter] object.
     * @throws java.io.IOException if any.
     */
    @Throws(IOException::class)
    fun nl(): CodeFileWriter {
        fw.write("\n")
        appendIdent()
        return this
    }

    /**
     *
     * append.
     *
     * @param obj a [java.lang.Object] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeFileWriter] object.
     * @throws java.io.IOException if any.
     */
    @Throws(IOException::class)
    fun append(obj: Any): CodeFileWriter {
        fw.write(obj.toString())
        return this
    }

    /**
     *
     * append.
     *
     * @param obj a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeFileWriter] object.
     * @throws java.io.IOException if any.
     */
    @Throws(IOException::class)
    fun append(obj: String): CodeFileWriter {
        fw.write(obj)
        return this
    }

    /**
     *
     * append.
     *
     * @param f a float.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeFileWriter] object.
     * @throws java.io.IOException if any.
     */
    @Throws(IOException::class)
    fun append(f: Float): CodeFileWriter {
        fw.write(f.toString())
        return this
    }


    /**
     *
     * append.
     *
     * @param d a double.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeFileWriter] object.
     * @throws java.io.IOException if any.
     */
    @Throws(IOException::class)
    fun append(d: Double): CodeFileWriter {
        fw.write(d.toString())
        return this
    }

    /**
     *
     * append.
     *
     * @param str an array of char.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeFileWriter] object.
     * @throws java.io.IOException if any.
     */
    @Throws(IOException::class)
    fun append(str: CharArray): CodeFileWriter {
        fw.write(str)
        return this
    }

    /**
     *
     * append.
     *
     * @param str an array of char.
     * @param offset a int.
     * @param len a int.
     * @return a [edu.kit.iti.formal.automation.st.util.CodeFileWriter] object.
     * @throws java.io.IOException if any.
     */
    @Throws(IOException::class)
    fun append(str: CharArray, offset: Int, len: Int): CodeFileWriter {
        fw.write(str, offset, len)
        return this
    }
}

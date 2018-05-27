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

import edu.kit.iti.formal.automation.visitors.Sections

import java.util.Stack

/**
 *
 * HTMLCodeWriter class.
 *
 * @author weigl
 * @version $Id: $Id
 */
class HTMLCodeWriter : CodeWriter() {

    private var lastSeperatorInsertPosition: Int = 0
    private val lastIsDiv = Stack<Boolean>()

    /**
     *
     * div.
     *
     * @param clazzes a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    operator fun div(clazzes: String): HTMLCodeWriter {
        sb.append("<div class=\"").append(clazzes.toLowerCase()).append("\">")
        lastIsDiv.push(true)
        return this
    }

    /**
     *
     * span.
     *
     * @param clazzes a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun span(clazzes: String): HTMLCodeWriter {
        sb.append("<span class=\"")
                .append(clazzes.toLowerCase())
                .append("\">")
        lastIsDiv.push(false)
        return this
    }

    /**
     *
     * end.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun end(): HTMLCodeWriter {
        sb.append(if (lastIsDiv.pop()) "</div>" else "</span>")
        return this
    }

    /**
     *
     * indent.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun indent(): HTMLCodeWriter {
        div("indent")
        return this
    }

    /**
     *
     * appendHtmlPreamble.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun appendHtmlPreamble(): HTMLCodeWriter {
        //		String style = "";
        //		try {
        //			style = FileUtils.readFileToString(new File("share/style.css"));
        //		} catch (IOException e) {
        //			e.printStackTrace();
        //		}

        val s = ("<!DOCTYPE html>\n" + "<html>\n" + "<head lang=\"en\">\n" + "    <meta charset=\"UTF-8\">\n"
                + "    <title></title>\n"
                + "    <link rel=\"stylesheet/less\" type=\"text/css\" href=\"style.less\"/>\n"
                + "    <script src=\"less.js\"></script>" + "    <link href=\"style.css\"/>" + "<style>" + ""
                + "</style>" + "</head>\n" + "<body>")
        append(s)
        return this
    }

    /**
     *
     * div.
     *
     * @param a a [edu.kit.iti.formal.automation.visitors.Sections] object.
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun div(vararg a: Sections): HTMLCodeWriter {
        for (b in a) {
            div(b.name.toLowerCase())
        }
        return this
    }

    /**
     *
     * span.
     *
     * @param a a [edu.kit.iti.formal.automation.visitors.Sections] object.
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun span(vararg a: Sections): HTMLCodeWriter {
        for (b in a) {
            span(b.name)
        }
        return this
    }

    /** {@inheritDoc}  */
    override fun keyword(word: String): HTMLCodeWriter {
        span(word).span(Sections.KEYWORD)
        super.keyword(word)
        return end().end()
    }

    /**
     *
     * seperator.
     *
     * @param s a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun seperator(s: String): HTMLCodeWriter {
        lastSeperatorInsertPosition = length
        span(Sections.SEPARATOR).append(s)
        return this.end()
    }

    /**
     *
     * variable.
     *
     * @param variable a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun variable(variable: String): HTMLCodeWriter {
        if (variable.contains("$")) {
            span(Sections.SPECIAL_VARIABLE).span(Sections.VARIABLE).append(variable)
            return this.end().end()
        }
        span(Sections.VARIABLE).append(variable)
        return this.end()
    }

    /**
     *
     * ts.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun ts(): HTMLCodeWriter {
        return seperator(";")
    }

    /**
     *
     * type.
     *
     * @param baseTypeName a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun type(baseTypeName: String): HTMLCodeWriter {
        span(Sections.TYPE_NAME).append(baseTypeName)
        return this.end()
    }

    /**
     *
     * operator.
     *
     * @param s a [java.lang.String] object.
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun operator(s: String): HTMLCodeWriter {
        span(Sections.OPERATOR).append(s)
        return this.end()
    }

    /**
     *
     * deleteLastSeparator.
     *
     * @return a [edu.kit.iti.formal.automation.st.util.HTMLCodeWriter] object.
     */
    fun deleteLastSeparator(): HTMLCodeWriter {
        sb.setLength(lastSeperatorInsertPosition)
        return this

    }

    companion object {
        private val serialVersionUID = -6017826265536761012L
    }
}

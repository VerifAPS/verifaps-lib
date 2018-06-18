package edu.kit.iti.formal.automation.st.util

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
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
import java.util.*


class HTMLCodeWriter : CodeWriter() {
    private var lastSeperatorInsertPosition: Int = 0
    private val lastIsDiv = Stack<Boolean>()

    operator fun div(clazzes: String): HTMLCodeWriter {
        sb.append("<div class=\"").append(clazzes.toLowerCase()).append("\">")
        lastIsDiv.push(true)
        return this
    }

    fun span(clazzes: String): HTMLCodeWriter {
        sb.append("<span class=\"")
                .append(clazzes.toLowerCase())
                .append("\">")
        lastIsDiv.push(false)
        return this
    }

    fun end(): HTMLCodeWriter {
        sb.append(if (lastIsDiv.pop()) "</div>" else "</span>")
        return this
    }

    fun indent(): HTMLCodeWriter {
        div("indent")
        return this
    }


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


    fun div(vararg a: Sections): HTMLCodeWriter {
        for (b in a) {
            div(b.name.toLowerCase())
        }
        return this
    }


    fun span(vararg a: Sections): HTMLCodeWriter {
        for (b in a) {
            span(b.name)
        }
        return this
    }


    override fun keyword(word: String): HTMLCodeWriter {
        span(word).span(Sections.KEYWORD)
        super.keyword(word)
        return end().end()
    }


    fun seperator(s: String): HTMLCodeWriter {
        lastSeperatorInsertPosition = length
        span(Sections.SEPARATOR).append(s)
        return this.end()
    }


    fun variable(variable: String): HTMLCodeWriter {
        if (variable.contains("$")) {
            span(Sections.SPECIAL_VARIABLE).span(Sections.VARIABLE).append(variable)
            return this.end().end()
        }
        span(Sections.VARIABLE).append(variable)
        return this.end()
    }


    fun ts(): HTMLCodeWriter {
        return seperator(";")
    }


    fun type(baseTypeName: String?): HTMLCodeWriter {
        span(Sections.TYPE_NAME).append(baseTypeName?:"<<<null>>>")
        return this.end()
    }


    fun operator(s: String): HTMLCodeWriter {
        span(Sections.OPERATOR).append(s)
        return this.end()
    }


    fun deleteLastSeparator(): HTMLCodeWriter {
        sb.setLength(lastSeperatorInsertPosition)
        return this

    }

    companion object {
        private val serialVersionUID = -6017826265536761012L
    }
}

package edu.kit.iti.formal.util

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

import java.util.*

/**
 *
 * Sections class.
 *
 * @author weigl
 */
enum class Sections {
    KEYWORD, STATEMENT, CASE_INTEGER_CONDITION, CASE_ENUM_CONDITION, OPERATOR, BINARY_EXPRESSION,
    ASSIGNMENT, TYPE_DECL_ENUM, TYPE_NAME, REPEAT, WHILE, UNARY_EXPRESSION, TYPE_DECL, CASE_STATEMENT, VARIABLE,
    SUBSCRIPT, STATEMENT_BLOCK, PROGRAM, VALUE, EXPRESSION_LIST, SEPARATOR, FUNC_CALL, FOR, FB, IFSTATEMENT, FB_CALL,
    CASE, TYPE_DECL_SIMPLE, VARIABLES_DEFINITION, COMMENT, TYPE_DECL_DECL, VARIABLES_DEFINITIONS, SPECIAL_VARIABLE, CONSTANT, ERROR
}

class HTMLCodeWriter : CodeWriter() {
    private val lastIsDiv = Stack<Boolean>()

    operator fun div(clazzes: String): HTMLCodeWriter {
        stream.append("<div class=\"").append(clazzes.toLowerCase()).append("\">")
        lastIsDiv.push(true)
        return this
    }

    fun span(clazzes: String): HTMLCodeWriter {
        stream.append("<span class=\"")
                .append(clazzes.toLowerCase())
                .append("\">")
        lastIsDiv.push(false)
        return this
    }

    fun end(): HTMLCodeWriter {
        stream.append(if (lastIsDiv.pop()) "</div>" else "</span>")
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
        printf(s)
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
        span(Sections.SEPARATOR).printf(s)
        return this.end()
    }


    fun variable(variable: String): HTMLCodeWriter {
        if (variable.contains("$")) {
            span(Sections.SPECIAL_VARIABLE).span(Sections.VARIABLE).printf(variable)
            return this.end().end()
        }
        span(Sections.VARIABLE).printf(variable)
        return this.end()
    }


    fun ts(): HTMLCodeWriter {
        return seperator(";")
    }


    fun type(baseTypeName: String?): HTMLCodeWriter {
        span(Sections.TYPE_NAME).printf(baseTypeName ?: "<<<null>>>")
        return this.end()
    }


    fun operator(s: String): HTMLCodeWriter {
        span(Sections.OPERATOR).printf(s)
        return this.end()
    }
}
package edu.kit.iti.formal.automation.visitors

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

import edu.kit.iti.formal.automation.st.StructuredTextHtmlPrinter
import edu.kit.iti.formal.automation.st.StructuredTextPrinter
import edu.kit.iti.formal.automation.st.ast.PouElements

/**
 *
 * VFactory class.
 *
 * @author weigla (04.07.2014)
 * @version $Id: $Id
 */
object VFactory {
    fun ast2Html(elements: Visitable, comments: Boolean): String {
        val stp = StructuredTextHtmlPrinter()
        stp.isPrintComments = comments
        stp.preamble()
        elements.accept(stp)
        stp.closeHtml()
        return stp.string
    }

    /**
     *
     * ast2St.
     *
     * @param a a [edu.kit.iti.formal.automation.visitors.Visitable] object.
     * @param comments a boolean.
     * @return a [java.lang.String] object.
     */
    @JvmOverloads
    fun ast2St(a: Visitable?, comments: Boolean = true): String {
        if (a == null) return ""
        val s = StructuredTextPrinter()
        s.isPrintComments = comments
        a.accept(s)
        return s.string
    }

    /**
     *
     * ast2St.
     *
     * @param st0ast a [edu.kit.iti.formal.automation.st.ast.PouElements] object.
     * @param comments a boolean.
     * @return a [java.lang.String] object.
     */
    fun ast2St(st0ast: PouElements, comments: Boolean): String {
        val stp = StructuredTextPrinter()
        stp.isPrintComments = comments
        st0ast.accept(stp)
        return stp.string
    }

    /**
     *
     * ast2Html.
     *
     * @param st0ast a [edu.kit.iti.formal.automation.st.ast.PouElements] object.
     * @param comments a boolean.
     * @return a [java.lang.String] object.
     */
    fun ast2Html(st0ast: PouElements, comments: Boolean): String {
        val stp = StructuredTextHtmlPrinter()
        stp.isPrintComments = comments
        stp.preamble()
        st0ast.accept(stp)
        stp.closeHtml()
        return stp.string
    }
}

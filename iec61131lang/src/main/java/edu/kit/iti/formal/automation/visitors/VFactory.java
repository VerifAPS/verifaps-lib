package edu.kit.iti.formal.automation.visitors;

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

import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st.StructuredTextHtmlPrinter;
import edu.kit.iti.formal.automation.st.StructuredTextPrinter;

/**
 * <p>VFactory class.</p>
 *
 * @author weigla (04.07.2014)
 * @version $Id: $Id
 */
public class VFactory {
    /**
     * <p>ast2Html.</p>
     *
     * @param elements a {@link edu.kit.iti.formal.automation.visitors.Visitable} object.
     * @param comments a boolean.
     * @return a {@link java.lang.String} object.
     */
    public static String ast2Html(Visitable elements, boolean comments) {
        StructuredTextHtmlPrinter stp = new StructuredTextHtmlPrinter();
        stp.setPrintComments(comments);
        stp.preamble();
        elements.accept(stp);
        stp.closeHtml();
        return stp.getString();
    }

    /**
     * <p>ast2St.</p>
     *
     * @param a a {@link edu.kit.iti.formal.automation.visitors.Visitable} object.
     * @param comments a boolean.
     * @return a {@link java.lang.String} object.
     */
    public static String ast2St(Visitable a, boolean comments) {
        if (a == null) return "";
        StructuredTextPrinter s = new StructuredTextPrinter();
        s.setPrintComments(comments);
        a.accept(s);
        return s.getString();
    }

    /**
     * <p>ast2St.</p>
     *
     * @param a a {@link edu.kit.iti.formal.automation.visitors.Visitable} object.
     * @return a {@link java.lang.String} object.
     */
    public static String ast2St(Visitable a) {
        return ast2St(a, true);
    }

    /**
     * <p>ast2St.</p>
     *
     * @param st0ast a {@link edu.kit.iti.formal.automation.st.ast.TopLevelElements} object.
     * @param comments a boolean.
     * @return a {@link java.lang.String} object.
     */
    public static String ast2St(TopLevelElements st0ast, boolean comments) {
        StructuredTextPrinter stp = new StructuredTextPrinter();
        stp.setPrintComments(comments);
        st0ast.accept(stp);
        return stp.getString();
    }

    /**
     * <p>ast2Html.</p>
     *
     * @param st0ast a {@link edu.kit.iti.formal.automation.st.ast.TopLevelElements} object.
     * @param comments a boolean.
     * @return a {@link java.lang.String} object.
     */
    public static String ast2Html(TopLevelElements st0ast, boolean comments) {
        StructuredTextHtmlPrinter stp = new StructuredTextHtmlPrinter();
        stp.setPrintComments(comments);
        stp.preamble();
        st0ast.accept(stp);
        stp.closeHtml();
        return stp.getString();
    }
}

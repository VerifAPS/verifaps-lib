package edu.kit.iti.formal.automation.visitors;

import edu.kit.iti.formal.automation.ast.TopLevelElements;

/**
 * @author weigla
 * @date 04.07.2014
 */
public class VFactory {
    public static String ast2Html(Visitable elements, boolean comments) {
        StructuredTextHtmlPrinter stp = new StructuredTextHtmlPrinter();
        stp.setPrintComments(comments);
        stp.preamble();
        elements.visit(stp);
        stp.closeHtml();
        return stp.getString();
    }

    public static String ast2St(Visitable a, boolean comments) {
        if (a == null) return "";
        StructuredTextPrinter s = new StructuredTextPrinter();
        s.setPrintComments(comments);
        a.visit(s);
        return s.getString();
    }

    public static String ast2St(Visitable a) {
        return ast2St(a, true);
    }

    public static String ast2St(TopLevelElements st0ast, boolean comments) {
        StructuredTextPrinter stp = new StructuredTextPrinter();
        stp.setPrintComments(comments);
        st0ast.visit(stp);
        return stp.getString();
    }

    public static String ast2Html(TopLevelElements st0ast, boolean comments) {
        StructuredTextHtmlPrinter stp = new StructuredTextHtmlPrinter();
        stp.setPrintComments(comments);
        stp.preamble();
        st0ast.visit(stp);
        stp.closeHtml();
        return stp.getString();
    }
}

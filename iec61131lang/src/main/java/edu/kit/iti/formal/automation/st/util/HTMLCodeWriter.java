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

import edu.kit.iti.formal.automation.visitors.Sections;

import java.util.Stack;

/**
 * <p>HTMLCodeWriter class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class HTMLCodeWriter extends CodeWriter {
    private static final long serialVersionUID = -6017826265536761012L;

    private int lastSeperatorInsertPosition;
    private Stack<Boolean> lastIsDiv = new Stack<>();

    /**
     * <p>div.</p>
     *
     * @param clazzes a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter div(String clazzes) {
        sb.append("<div class=\"").append(clazzes.toLowerCase()).append("\">");
        lastIsDiv.push(true);
        return this;
    }

    /**
     * <p>span.</p>
     *
     * @param clazzes a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter span(String clazzes) {
        sb.append("<span class=\"")
                .append(clazzes.toLowerCase())
                .append("\">");
        lastIsDiv.push(false);
        return this;
    }

    /**
     * <p>end.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter end() {
        sb.append(lastIsDiv.pop() ? "</div>" : "</span>");
        return this;
    }

    /**
     * <p>indent.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter indent() {
        div("indent");
        return this;
    }

    /**
     * <p>appendHtmlPreamble.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter appendHtmlPreamble() {
//		String style = "";
//		try {
//			style = FileUtils.readFileToString(new File("share/style.css"));
//		} catch (IOException e) {
//			e.printStackTrace();
//		}

        String s = "<!DOCTYPE html>\n" + "<html>\n" + "<head lang=\"en\">\n" + "    <meta charset=\"UTF-8\">\n"
                + "    <title></title>\n"
                + "    <link rel=\"stylesheet/less\" type=\"text/css\" href=\"style.less\"/>\n"
                + "    <script src=\"less.js\"></script>" + "    <link href=\"style.css\"/>" + "<style>" + ""
                + "</style>" + "</head>\n" + "<body>";
        append(s);
        return this;
    }

    /**
     * <p>div.</p>
     *
     * @param a a {@link edu.kit.iti.formal.automation.visitors.Sections} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter div(Sections... a) {
        for (Sections b : a) {
            div(b.name().toLowerCase());
        }
        return this;
    }

    /**
     * <p>span.</p>
     *
     * @param a a {@link edu.kit.iti.formal.automation.visitors.Sections} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter span(Sections... a) {
        for (Sections b : a) {
            span(b.name());
        }
        return this;
    }

    /** {@inheritDoc} */
    public HTMLCodeWriter keyword(String word) {
        span(word).span(Sections.KEYWORD);
        super.keyword(word);
        return end().end();
    }

    /**
     * <p>seperator.</p>
     *
     * @param s a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter seperator(String s) {
        lastSeperatorInsertPosition = length();
        span(Sections.SEPARATOR).append(s);
        return this.end();
    }

    /**
     * <p>variable.</p>
     *
     * @param variable a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter variable(String variable) {
        if (variable.contains("$")) {
            span(Sections.SPECIAL_VARIABLE).span(Sections.VARIABLE).append(variable);
            return this.end().end();
        }
        span(Sections.VARIABLE).append(variable);
        return this.end();
    }

    /**
     * <p>ts.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter ts() {
        return seperator(";");
    }

    /**
     * <p>type.</p>
     *
     * @param baseTypeName a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter type(String baseTypeName) {
        span(Sections.TYPE_NAME).append(baseTypeName);
        return this.end();
    }

    /**
     * <p>operator.</p>
     *
     * @param s a {@link java.lang.String} object.
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter operator(String s) {
        span(Sections.OPERATOR).append(s);
        return this.end();
    }

    /**
     * <p>deleteLastSeparator.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.util.HTMLCodeWriter} object.
     */
    public HTMLCodeWriter deleteLastSeparator() {
        sb.setLength(lastSeperatorInsertPosition);
        return this;

    }
}

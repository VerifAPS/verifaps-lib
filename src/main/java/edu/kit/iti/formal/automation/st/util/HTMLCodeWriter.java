package edu.kit.iti.formal.automation.st.util;

import edu.kit.iti.formal.automation.visitors.Sections;

import java.util.Stack;

public class HTMLCodeWriter extends CodeWriter {
    private static final long serialVersionUID = -6017826265536761012L;

    private int lastSeperatorInsertPosition;
    private Stack<Boolean> lastIsDiv = new Stack<>();

    public HTMLCodeWriter div(String clazzes) {
        sb.append("<div class=\"").append(clazzes.toLowerCase()).append("\">");
        lastIsDiv.push(true);
        return this;
    }

    public HTMLCodeWriter span(String clazzes) {
        sb.append("<span class=\"")
                .append(clazzes.toLowerCase())
                .append("\">");
        lastIsDiv.push(false);
        return this;
    }

    public HTMLCodeWriter end() {
        sb.append(lastIsDiv.pop() ? "</div>" : "</span>");
        return this;
    }

    public HTMLCodeWriter indent() {
        div("indent");
        return this;
    }

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

    public HTMLCodeWriter div(Sections... a) {
        for (Sections b : a) {
            div(b.name().toLowerCase());
        }
        return this;
    }

    public HTMLCodeWriter span(Sections... a) {
        for (Sections b : a) {
            span(b.name());
        }
        return this;
    }

    public HTMLCodeWriter keyword(String word) {
        span(word).span(Sections.KEYWORD);
        super.keyword(word);
        return end().end();
    }

    public HTMLCodeWriter seperator(String s) {
        lastSeperatorInsertPosition = length();
        span(Sections.SEPARATOR).append(s);
        return this.end();
    }

    public HTMLCodeWriter variable(String variable) {
        if (variable.contains("$")) {
            span(Sections.SPECIAL_VARIABLE).span(Sections.VARIABLE).append(variable);
            return this.end().end();
        }
        span(Sections.VARIABLE).append(variable);
        return this.end();
    }

    public HTMLCodeWriter ts() {
        return seperator(";");
    }

    public HTMLCodeWriter type(String baseTypeName) {
        span(Sections.TYPE_NAME).append(baseTypeName);
        return this.end();
    }

    public HTMLCodeWriter operator(String s) {
        span(Sections.OPERATOR).append(s);
        return this.end();
    }

    public HTMLCodeWriter deleteLastSeparator() {
        sb.setLength(lastSeperatorInsertPosition);
        return this;

    }
}
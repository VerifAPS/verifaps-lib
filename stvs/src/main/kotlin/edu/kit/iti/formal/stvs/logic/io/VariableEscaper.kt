package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.stvs.model.code.Code;
import org.antlr.v4.runtime.Token;

import java.util.regex.Pattern;

/**
 * This class is used to escape identifiers for the GeTeTa verification engine.
 *
 * @author Benjamin Alt
 * @author Alexander Weigl
 * @deprecated Disabled due to bugs with enum constant.
 */

@Deprecated()
public class VariableEscaper {

    private static final Pattern NUMBER_PATTERN = Pattern.compile("-?[0-9]+");
    private static final Pattern BOOL_PATTERN = Pattern.compile("(TRUE)|(FALSE)");
    private static final String PREFIX = "var_";

    /**
     * Prepends an escaping prefix to a given identifier.
     *
     * @param identifier identifier that should be escaped.
     * @return escaped identifier
     */
    public static String escapeIdentifier(String identifier) {
        return identifier;

    /*if (!NUMBER_PATTERN.matcher(identifier).matches()
        && !BOOL_PATTERN.matcher(identifier).matches()) {
      return PREFIX + identifier;
    }
    return identifier;*/
    }

    /**
     * Escapes an expression that can be parsed by ANTLR.
     *
     * @param expr expression to be escaped.
     * @return escaped expression
     */
    public static String escapeCellExpression(String expr) {
        return expr;
    /*CharStream charStream = new ANTLRInputStream(expr);
    CellExpressionLexer lexer = new CellExpressionLexer(charStream);
    String result = expr;
    int currentOffset = 0;
    for (Token token : lexer.getAllTokens()) {
      if (token.getType() == CellExpressionLexer.IDENTIFIER) {
        int begin = token.getStartIndex() + currentOffset;
        int end = token.getStopIndex() + currentOffset;
        String before = result.substring(0, begin);
        String after = result.substring(end + 1, result.length());
        result = before + PREFIX + token.getText() + after;
        currentOffset += PREFIX.length();
      }
    }
    return result;*/
    }

    /**
     * Escapes code by lexing it and treating identifiers accordingly.
     *
     * @param code code that should be escaped
     * @return escaped code
     */
    public static String escapeCode(Code code) {
        StringBuilder res = new StringBuilder("");
        for (Token token : code.getTokens()) {
            if (token.getType() == IEC61131Lexer.IDENTIFIER) {
                res.append(escapeIdentifier(token.getText()));
            } else if (token.getType() == IEC61131Lexer.CAST_LITERAL) {
                res.append(escapeEnumReference(token.getText()));
            } else {
                res.append(token.getText());
            }
        }
        return res.toString();
    }

    private static String escapeEnumReference(String tokenText) {
        String[] tokens = tokenText.split("#");
        if (tokens.length != 2) {
            return escapeIdentifier(tokenText);
        }
        return escapeIdentifier(tokens[0]) + "#" + escapeIdentifier(tokens[1]);
    }

    /**
     * Removes escaping from an identifier.
     *
     * @param varName identifier from which the escaping should be removed.
     * @return unescaped identifier
     */
    public static String unescapeIdentifier(String varName) {
        if (varName.startsWith(PREFIX)) {
            return varName.substring(PREFIX.length());
        }
        return varName;
    }
}

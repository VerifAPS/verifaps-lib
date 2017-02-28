package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.expressions.parser.CellExpressionLexer;

import java.util.regex.Pattern;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;

/**
 * This class is used to escape identifiers for the geteta verification engine.
 *
 * @author Benjamin Alt
 */
public class VariableEscaper {

  private static final Pattern NUMBER_PATTERN = Pattern.compile("-?[0-9]+");
  private static final Pattern BOOL_PATTERN = Pattern.compile("(TRUE)|(FALSE)");

  /**
   * Prepends "_var" to a {@code name}.
   *
   * @param name name that should be escaped.
   * @return escaped name
   */
  public static String escapeName(String name) {
    if (NUMBER_PATTERN.matcher(name).matches() || BOOL_PATTERN.matcher(name).matches()) {
      return name;
    }
    return "var_" + name;
  }

  /**
   * Escapes an expression that can be parsed by ANTLR.
   *
   * @param expr expression to be escaped.
   * @return escaped expression
   */
  public static String escapeCellExpression(String expr) {
    CharStream charStream = new ANTLRInputStream(expr);
    CellExpressionLexer lexer = new CellExpressionLexer(charStream);
    String result = expr;
    int currentOffset = 0;
    for (Token token : lexer.getAllTokens()) {
      if (token.getType() == CellExpressionLexer.IDENTIFIER) {
        int begin = token.getStartIndex() + currentOffset;
        int end = token.getStopIndex() + currentOffset;
        String before = result.substring(0, begin);
        String after = result.substring(end + 1, result.length());
        result = before + "var_" + token.getText() + after;
        currentOffset += 4; // 4 <-- length of "var_"
      }
    }
    return result;
  }

  /**
   * Escapes code by lexing it and treating identifiers accordingly.
   *
   * @param code code that should be escaped
   * @return escaped code
   */
  public static String escapeCode(Code code) {
    String res = "";
    for (Token token : code.getTokens()) {
      if (token.getType() == IEC61131Lexer.IDENTIFIER) {
        res += escapeName(token.getText());
      } else {
        res += token.getText();
      }
    }
    return res;
  }

  /**
   * Removes escaping from a name.
   *
   * @param varName name from which the escaping should be removed.
   * @return unescaped name
   */
  public static String unescapeName(String varName) {
    if (varName.startsWith("var_")) {
      return varName.substring(4);
    }
    return varName;
  }
}

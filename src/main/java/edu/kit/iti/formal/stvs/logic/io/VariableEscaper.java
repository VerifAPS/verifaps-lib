package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.expressions.parser.CellExpressionLexer;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CharStream;
import org.antlr.v4.runtime.Token;
import org.antlr.v4.runtime.TokenStream;

import java.util.regex.Pattern;

/**
 * Created by bal on 12.02.17.
 */
public class VariableEscaper {

  private final static String IDENTIFIER_RE = "[$a-zA-Z0-9_]+";
  private final static Pattern IDENTIFIER_PATTERN = Pattern.compile("(?!TRUE)(?!FALSE)" +
      "(?!-?[0-9]+)" +
      IDENTIFIER_RE);

  public static String escapeName(String name) {
    return "var_" + name;
  }

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

  public static String unescapeName(String varName) {
    if (varName.startsWith("var_")) {
      return varName.substring(4);
    }
    return varName;
  }
}

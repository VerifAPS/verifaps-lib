package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.stvs.model.code.Code;
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
    String currentBuf = "";
    String lastMatch = "";
    String outBuf = "";
    for (int i = 0; i < expr.length(); i++) {
      char c = expr.charAt(i);
      currentBuf += c;
      if (!IDENTIFIER_PATTERN.matcher(currentBuf).matches()) {
        if (currentBuf.length() > 1) {
          // I have either a valid identifier plus an operator or TRUE or FALSE in the buffer
          if (currentBuf.equals("TRUE") || currentBuf.equals("FALSE")) {
            outBuf += currentBuf;
          } else {
            outBuf += currentBuf.replaceAll(IDENTIFIER_PATTERN.toString(), escapeName(lastMatch));
          }
        } else {
          outBuf += currentBuf;
        }
        currentBuf = "";
      } else {
        lastMatch = currentBuf;
        if(i == expr.length()-1) {
          outBuf += currentBuf.replaceAll(IDENTIFIER_PATTERN.toString(), escapeName(lastMatch));
        }
      }
    }
    return outBuf;
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

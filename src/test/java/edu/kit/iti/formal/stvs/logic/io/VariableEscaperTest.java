package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.code.Code;
import org.junit.Test;

import java.util.HashMap;
import java.util.Map;

import static org.junit.Assert.assertEquals;

/**
 * Created by bal on 12.02.17.
 */
public class VariableEscaperTest {

  @Test
  public void testEscapeCellExpression() {
    Map<String, String> expressions = new HashMap<>();
    expressions.put("lala+lala / blabla", "var_lala+var_lala / var_blabla");
    expressions.put("lala+lalala / la", "var_lala+var_lalala / var_la");
    expressions.put("=TRUE", "=TRUE");
    expressions.put("lala != TRUE, lalala = FALSE", "var_lala != TRUE, var_lalala = FALSE");
    expressions.put("lala[-2]+lalala[-1]", "var_lala[-2]+var_lalala[-1]");
    expressions.put("lalala AND lalala", "var_lalala AND var_lalala");
    expressions.put("ANDiamavariable AND iANDamORaVariable", "var_ANDiamavariable AND " +
        "var_iANDamORaVariable");
    for (String expr : expressions.keySet()) {
      String res = VariableEscaper.escapeCellExpression(expr);
      assertEquals(expressions.get(expr), res);
    }
  }

  @Test
  public void testEscapeEnumReference() {
    Code code = new Code();
    code.updateSourcecode("TYPE\n" +
        "  TrafficLight : (Red, Green);\n" +
        "END_TYPE\n" +
        "\n" +
        "PROGRAM PedestrianTrafficLight\n" +
        "\n" +
        "  VAR_INPUT\n" +
        "    pedBtnPress : BOOL;\n" +
        "  END_VAR\n" +
        "  \n" +
        "  VAR_OUTPUT\n" +
        "    carLight : TrafficLight;\n" +
        "    pedLight : TrafficLight;\n" +
        "    counter  : INT;\n" +
        "  END_VAR\n" +
        "  carLight := TrafficLight#Red;\n" +
        "END_PROGRAM");
    String expected = "TYPE\n" +
        "  var_TrafficLight : (var_Red, var_Green);\n" +
        "END_TYPE\n" +
        "\n" +
        "PROGRAM var_PedestrianTrafficLight\n" +
        "\n" +
        "  VAR_INPUT\n" +
        "    var_pedBtnPress : BOOL;\n" +
        "  END_VAR\n" +
        "  \n" +
        "  VAR_OUTPUT\n" +
        "    var_carLight : var_TrafficLight;\n" +
        "    var_pedLight : var_TrafficLight;\n" +
        "    var_counter  : INT;\n" +
        "  END_VAR\n" +
        "  var_carLight := var_TrafficLight#var_Red;\n" +
        "END_PROGRAM";
    assertEquals(expected, VariableEscaper.escapeCode(code));
  }

  @Test
  public void testEscapeCode() {
    Code code = new Code();
    code.updateSourcecode("TYPE\n" +
        "  enumD : (literalOne, literalTwo);\n" +
        "END_TYPE\n" +
        "\n" +
        "PROGRAM constantprogram\n" +
        "  VAR_INPUT\n" +
        "    A : INT;\n" +
        "    B : BOOL;\n" +
        "  END_VAR\n" +
        "\n" +
        "  VAR_OUTPUT\n" +
        "    C : INT;\n" +
        "    D : enumD;\n" +
        "  END_VAR\n" +
        "\n" +
        "  C := 52;\n" +
        "END_PROGRAM");
    String expected = "TYPE\n" +
        "  var_enumD : (var_literalOne, var_literalTwo);\n" +
        "END_TYPE\n" +
        "\n" +
        "PROGRAM var_constantprogram\n" +
        "  VAR_INPUT\n" +
        "    var_A : INT;\n" +
        "    var_B : BOOL;\n" +
        "  END_VAR\n" +
        "\n" +
        "  VAR_OUTPUT\n" +
        "    var_C : INT;\n" +
        "    var_D : var_enumD;\n" +
        "  END_VAR\n" +
        "\n" +
        "  var_C := 52;\n" +
        "END_PROGRAM";
    assertEquals(expected, VariableEscaper.escapeCode(code));
  }
}
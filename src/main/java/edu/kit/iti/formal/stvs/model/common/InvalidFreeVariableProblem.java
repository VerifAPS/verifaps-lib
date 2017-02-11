package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.expressions.VariableExpr;
import org.apache.commons.lang3.StringEscapeUtils;

import java.util.Map;

/**
 * Created by philipp on 09.02.17.
 */
public class InvalidFreeVariableProblem extends FreeVariableProblem {

  public static ValidFreeVariable tryToConvertToValid(
      FreeVariable freeVariable, Map<String, Type> typesByName)
      throws InvalidFreeVariableProblem {
    String validName = tryToGetValidName(freeVariable);
    Type validType = tryToGetValidType(freeVariable, typesByName);
    Value validDefaultValue = tryToGetValidDefaultValue(freeVariable, validType, typesByName);
    return new ValidFreeVariable(validName, validType, validDefaultValue);
  }

  private static String tryToGetValidName(FreeVariable freeVariable)
      throws InvalidFreeVariableProblem {
    String varName = freeVariable.getName();
    if (VariableExpr.IDENTIFIER_PATTERN.matcher(varName).matches()) {
      return varName;
    } else {
      throw new InvalidFreeVariableProblem(
          "Variable has illegal characters in name: "
          + StringEscapeUtils.escapeJava(varName));
    }
  }

  private static Type tryToGetValidType(
      FreeVariable freeVariable, Map<String, Type> typesByName)
      throws InvalidFreeVariableProblem {
    Type foundType = typesByName.get(freeVariable.getType());
    if (foundType == null) {
      throw new InvalidFreeVariableProblem("Variable has unknown type: "
          + StringEscapeUtils.escapeJava(freeVariable.getType()));
    }
    return foundType;
  }

  private static Value tryToGetValidDefaultValue(FreeVariable freeVariable, Type freeVarType, Map<String, Type> typesByName)
      throws InvalidFreeVariableProblem {
    if (freeVariable.getDefaultValue().isEmpty()) {
      return null;
    }
    return freeVarType.parseLiteral(freeVariable.getDefaultValue().trim())
        .orElseThrow(() -> new InvalidFreeVariableProblem(
            "Couldn't parse default value: "
                + StringEscapeUtils.escapeJava(freeVariable.getDefaultValue())));
  }

  protected InvalidFreeVariableProblem(String errorMessage) {
    super(errorMessage);
  }

  @Override
  public String getProblemName() {
    return "invalid free variable";
  }

}

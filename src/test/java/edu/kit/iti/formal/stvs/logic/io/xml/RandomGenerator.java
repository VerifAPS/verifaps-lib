package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import org.apache.commons.lang3.RandomStringUtils;

import java.io.ByteArrayOutputStream;
import java.io.UnsupportedEncodingException;
import java.util.*;

/**
 * @author Benjamin Alt
 */
public class RandomGenerator {

  private static final List<String> BOOLEAN_BINARY_OPS = Arrays.asList("AND", "OR", "XOR");
  private static final List<String> INTEGER_BINARY_OPS = Arrays.asList("/", "*", "-", "+", "MOD");
  private static final List<String> COMPARISON_OPS = Arrays.asList("=", ">", "<", "<=", ">=");

  private static final int MAX_IDENTIFIER_LENGTH = 5;
  private static final int MAX_ENUM_LITERALS = 4;
  private static final int MAX_COMMENT_LENGTH = 10;
  private static final int MAX_NAME_LENGTH = 10;
  private static final int MAX_INT = 32767;
  private Random random;
  private List<TypeEnum> enumTypes;

  public RandomGenerator() {
    random = new Random();
    enumTypes = new ArrayList<>();
  }

  public RandomGenerator(long seed) {
    random = new Random(seed);
    enumTypes = new ArrayList<>();
  }

  public ConstraintSpecification randomConstraintSpec(int columns, int rows, int freeVariables) {
    FreeVariableList freeVariableList = new FreeVariableList();
    for (int i = 0; i < freeVariables; i++) {
      freeVariableList.getVariables().add(randomFreeVariable(freeVariableList));
    }
    ConstraintSpecification constraintSpec = new ConstraintSpecification(freeVariableList);
    constraintSpec.setName(RandomStringUtils.random(random.nextInt(MAX_NAME_LENGTH - 1) + 1));
    constraintSpec.setComment(RandomStringUtils.random(random.nextInt(MAX_COMMENT_LENGTH - 1) +
        1));
    for (int i = 0; i < columns; i++) {
      constraintSpec.getColumnHeaders().add(randomSpecIoVariable(constraintSpec.getColumnHeaders()));
    }
    for (int i = 0; i < rows; i++) {
      constraintSpec.getRows().add(randomSpecificationRow(constraintSpec.getColumnHeaders(),
          freeVariableList));
      constraintSpec.getDurations().add(randomDuration());
    }
    return constraintSpec;
  }

  private ConstraintDuration randomDuration() {
    int randomInt = random.nextInt(10);
    if (randomInt < 3) {
      return new ConstraintDuration("-");
    }
    if (randomInt < 6) {
      int lowerBound = random.nextInt(10);
      return new ConstraintDuration("[" + Integer.toString(lowerBound) + "," + Integer.toString
          (lowerBound + random.nextInt(10)) + "]");
    }
    return new ConstraintDuration("[" + Integer.toString(random.nextInt(10)) + ",-]");
  }

  private SpecificationRow<ConstraintCell> randomSpecificationRow(List<SpecIoVariable> columnHeaders, FreeVariableList freeVariableList) {
    Map<String, ConstraintCell> cells = new HashMap<>();
    for (SpecIoVariable ioVariable : columnHeaders) {
      ConstraintCell cell = randomConstraintCell(ioVariable, columnHeaders, freeVariableList);
      cells.put(ioVariable.getName(), cell);
    }
    SpecificationRow<ConstraintCell> row = new SpecificationRow<>(cells, p -> new javafx.beans.Observable[0]);
    row.setComment(RandomStringUtils.random(MAX_COMMENT_LENGTH));
    return row;
  }

  private ConstraintCell randomConstraintCell(SpecIoVariable ioVariable,
                                              List<SpecIoVariable> columnHeaders,
                                              FreeVariableList freeVariableList) {
    String cellString = "";
    int randomInt = random.nextInt(10);
    if (randomInt < 3) {
      cellString = randomAssignment(ioVariable, columnHeaders, freeVariableList);
    } else if (randomInt < 8) {
      cellString = randomBooleanExpression(columnHeaders, freeVariableList);
    } else {
      cellString = "-"; // Wildcard with probability 10%
    }
    return new ConstraintCell(cellString);
  }

  private String randomAssignment(SpecIoVariable ioVariable, List<SpecIoVariable> columnHeaders, FreeVariableList freeVariableList) {
    return "=" + randomExpressionOfType(ioVariable, columnHeaders, freeVariableList);
  }

  private String randomExpressionOfType(SpecIoVariable ioVariable, List<SpecIoVariable> columnHeaders,
                                        FreeVariableList freeVariableList) {
    switch(ioVariable.getType()) {
      case "INT":
        return randomIntegerExpression(columnHeaders, freeVariableList);
      case "BOOL":
        return randomBooleanExpression(columnHeaders, freeVariableList);
      default:
        return randomEnumExpression(ioVariable, columnHeaders, freeVariableList);
    }
  }

  private String randomEnumExpression(SpecIoVariable ioVariable, List<SpecIoVariable>
      columnHeaders, FreeVariableList freeVariableList) {
    // Enums can only be compared --> boolean expression
    // So the only expression of enum value is a single enum literal
    TypeEnum enumType = null;
    for (TypeEnum type : enumTypes) {
      if (ioVariable.getType().equals(type.getTypeName())) {
        enumType = type;
      }
    }
    if (enumType == null) throw new IllegalStateException("Enum type not found!");
    return enumType.getValues().get(random.nextInt(enumType.getValues().size())).getValueString();
  }

  private String randomIntegerExpression(List<SpecIoVariable> columnHeaders, FreeVariableList
      freeVariableList) {
    int randomInt = random.nextInt(10);
    if (randomInt == 1) {
      // random unary expression - there is only one, unary minus
      return "-(" + randomIntegerExpression(columnHeaders, freeVariableList) + ")";
    }
    if (randomInt == 2) {
     // random binary expression
      return "(" + randomIntegerExpression(columnHeaders, freeVariableList) + " " +
          randomIntegerBinaryOp() + " " + randomIntegerExpression(columnHeaders, freeVariableList)
          + ")";
    }
    if (randomInt == 3) {
      // back reference or variable
      List<String> intVariables = new ArrayList<>();
      for (SpecIoVariable var : columnHeaders) {
        if (var.getType().equals("INT")) {
          intVariables.add(var.getName());
        }
      }
      if (intVariables.size() == 0) return Integer.toString(random.nextInt(MAX_INT));
      String varName = intVariables.get(random.nextInt(intVariables.size()));
      int backReference = random.nextInt(10);
      if (random.nextBoolean()) {
        return varName + "[-" + Integer.toString(backReference) + "]";
      }
      return varName;
    }
    if (randomInt == 4) {
      // free variable
      List<String> intVariables = new ArrayList<>();
      for (FreeVariable freeVariable : freeVariableList.getVariables()) {
        if (freeVariable.getType().equals("INT")) {
          intVariables.add(freeVariable.getName());
        }
      }
      if (intVariables.size() == 0) return Integer.toString(random.nextInt(MAX_INT));
      return intVariables.get(random.nextInt(intVariables.size()));
    }
    // Default: Random integer
    return Integer.toString(random.nextInt(MAX_INT));
  }

  private String randomIntegerBinaryOp() {
    return INTEGER_BINARY_OPS.get(random.nextInt(INTEGER_BINARY_OPS.size()));
  }

  private String randomBooleanExpression(List<SpecIoVariable> columnHeaders,
                         FreeVariableList freeVariableList) {
    int randomInt = random.nextInt(10);
    if (randomInt == 0) {
      // random unary op
      return "NOT " + randomBooleanExpression(columnHeaders, freeVariableList);
    }
    if (randomInt == 1) {
      // random binary op
      return "(" + randomBooleanExpression(columnHeaders, freeVariableList) + " " +
          randomBooleanBinaryOp() + " " + randomBooleanExpression(columnHeaders, freeVariableList)
          + ")";
    }
    if (randomInt == 2) {
        return "(" + randomIntegerExpression(columnHeaders, freeVariableList) + " " +
            randomComparisonOp() + " " + randomIntegerExpression(columnHeaders, freeVariableList)
            + ")";
    }
    if (randomInt == 3) {
      // back reference or variable
      List<String> boolVariables = new ArrayList<>();
      for (SpecIoVariable var : columnHeaders) {
        if (var.getType().equals("BOOL")) {
          boolVariables.add(var.getName());
        }
      }
      if (boolVariables.size() == 0) return random.nextBoolean() ? "TRUE" : "FALSE";
      String varName = boolVariables.get(random.nextInt(boolVariables.size()));
      int backReference = random.nextInt(10);
      if (random.nextBoolean()) {
        return varName + "[-" + Integer.toString(backReference) + "]";
      }
      return varName;
    }
    if (randomInt == 4) {
      // free variable
      List<String> boolVariables = new ArrayList<>();
      for (FreeVariable freeVariable : freeVariableList.getVariables()) {
        if (freeVariable.getType().equals("BOOL")) {
          boolVariables.add(freeVariable.getName());
        }
      }
      if (boolVariables.size() == 0) return random.nextBoolean() ? "TRUE" : "FALSE";
      return boolVariables.get(random.nextInt(boolVariables.size()));
    }
    // Default: Random literal (TRUE/FALSE)
    return random.nextBoolean() ? "TRUE" : "FALSE";
  }

  private String randomComparisonOp() {
    return COMPARISON_OPS.get(random.nextInt(COMPARISON_OPS.size()));
  }

  private String randomBooleanBinaryOp() {
    return BOOLEAN_BINARY_OPS.get(random.nextInt(BOOLEAN_BINARY_OPS.size()));
  }

  private SpecIoVariable randomSpecIoVariable(List<SpecIoVariable> specIoVariables) {
    List specIoVariableNames = new ArrayList();
    for (SpecIoVariable var : specIoVariables) {
      specIoVariableNames.add(var.getName());
    }
    String name = nonConflictingName(specIoVariableNames);
    return new SpecIoVariable(randomCategory(), randomType().getTypeName(), name);
  }

  private VariableCategory randomCategory() {
    int randomInt = random.nextInt(2);
    if (randomInt == 0) {
      return VariableCategory.INPUT;
    }
    return VariableCategory.OUTPUT;
  }

  private FreeVariable randomFreeVariable(FreeVariableList freeVariableList) {
    List<String> freeVariableNames = new ArrayList<>();
    for (FreeVariable freeVar : freeVariableList.getVariables()) {
      freeVariableNames.add(freeVar.getName());
    }
    String name = nonConflictingName(freeVariableNames);
    Type type = randomType();
    Value defaultValue = type.generateDefaultValue();
    return new FreeVariable(name, type.getTypeName(), defaultValue.getValueString());
  }

  private Type randomType() {
    int randomInt = random.nextInt(10);
    if (randomInt < 3) {
      return TypeInt.INT;
    }
    if (randomInt < 6) {
      return TypeBool.BOOL;
    }
    return randomEnumType();
  }

  private Type randomEnumType() {
    if (random.nextBoolean() && enumTypes.size() > 0) {
      // Use an existing enum type
      return enumTypes.get(random.nextInt(enumTypes.size()));
    } else {
      // Create a new enum type
      int numberOfLiterals = random.nextInt(MAX_ENUM_LITERALS);
      String[] enumLiterals = new String[numberOfLiterals + 1];
      for (int i = 0; i <= numberOfLiterals; i++) {
        enumLiterals[i] = nonConflictingName(Arrays.asList(enumLiterals));
      }
      List<String> enumNames = new ArrayList<>();
      for (TypeEnum num : enumTypes) {
        enumNames.add(num.getTypeName());
      }
      TypeEnum newEnum = TypeFactory.enumOfName(nonConflictingName(enumNames),
          enumLiterals);
      enumTypes.add(newEnum);
      return newEnum;
    }
  }

  private String nonConflictingName(List<String> names) {
    String name = randomIdentifier();
    boolean nameConflicts = true;
    while (nameConflicts && names.size() > 0) {
      name = randomIdentifier();
      for (String possibleConflict : names) {
        if (name.equals(possibleConflict)) {
          nameConflicts = true;
          break;
        }
        nameConflicts = false;
      }
    }
    return name;
  }

  private String randomIdentifier() {
    StringBuilder id = new StringBuilder();
    id.append(randomNonNumeric());
    for (int i = 0; i < random.nextInt(MAX_IDENTIFIER_LENGTH - 1) + 1; i++) {
      id.append(randomAlphaNumeric());
    }
    return id.toString();
  }

  private String randomAlphaNumeric() {
    int randomInt = random.nextInt(10);
    if (randomInt < 2) {
      return RandomStringUtils.randomNumeric(1);
    }
    return randomNonNumeric();
  }

  private String randomNonNumeric() {
    int randomInt = random.nextInt(10);
    if (randomInt == 0) {
      return "$";
    }
    if (randomInt == 1) {
      return "_";
    }
    return RandomStringUtils.randomAlphabetic(1);
  }

  public static void main(String[] args) throws ExportException, UnsupportedEncodingException {
    RandomGenerator generator = new RandomGenerator();
    ConstraintSpecification constraintSpec = generator.randomConstraintSpec(4, 3, 1);
    ByteArrayOutputStream baos = ExporterFacade.exportSpec(constraintSpec, ExporterFacade.ExportFormat.XML);
    System.out.println(baos.toString("utf-8"));
  }
}

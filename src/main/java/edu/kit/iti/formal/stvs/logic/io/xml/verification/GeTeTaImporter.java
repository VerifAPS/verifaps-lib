package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.exteta_1_0.report.Assignment;
import edu.kit.iti.formal.exteta_1_0.report.Counterexample;
import edu.kit.iti.formal.exteta_1_0.report.Message;
import edu.kit.iti.formal.exteta_1_0.report.ObjectFactory;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.VariableEscaper;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlImporter;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.expressions.ValueBool;
import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.model.verification.VerificationError;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import edu.kit.iti.formal.stvs.model.verification.VerificationSuccess;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.regex.Pattern;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import javax.xml.transform.Transformer;
import javax.xml.transform.TransformerException;
import javax.xml.transform.TransformerFactory;
import javax.xml.transform.dom.DOMSource;
import javax.xml.transform.stream.StreamResult;

import org.w3c.dom.Node;

/**
 * Provides functionality to import the output of the GeTeTa verification engine.
 *
 * @author Benjamin Alt
 */
public class GeTeTaImporter extends XmlImporter<VerificationResult> {

  /* GeTeTa return codes */
  private static final String RETURN_CODE_SUCCESS = "verified";
  private static final String RETURN_CODE_NOT_VERIFIED = "not-verified";

  /* Regular expressions */
  private static final String IDENTIFIER_RE = "[$a-zA-Z0-9_]+";
  private static final Pattern VARIABLES_FOUND_PATTERN =
      Pattern.compile("[0-9]+ variables " + "found");
  private static final Pattern VARIABLE_DECL_PATTERN =
      Pattern.compile("\\s*" + IDENTIFIER_RE + " : " + IDENTIFIER_RE);
  private static final Pattern CODE_VARIABLE_PATTERN = Pattern.compile("code\\." + IDENTIFIER_RE);
  private static final Pattern INPUT_VARIABLE_PATTERN = Pattern.compile(IDENTIFIER_RE);
  private static final Pattern INT_VALUE_PATTERN = Pattern.compile("-?0sd16_-?[0-9]+");
  private static final Pattern BOOL_VALUE_PATTERN = Pattern.compile("(TRUE)|(FALSE)");

  private final List<Type> typeContext;
  private final ConstraintSpecification constraintSpecification;

  /**
   * Creates a new GeTeTaImporter.
   *
   * @param typeContext List of types available in the specification
   * @param constraintSpec The constraintSpecification for which this is a counterexample
   */
  public GeTeTaImporter(List<Type> typeContext, ConstraintSpecification constraintSpec) {
    this.typeContext = typeContext;
    this.constraintSpecification = constraintSpec;
  }

  /**
   * Imports a {@link VerificationResult} from an XML {@link Node}.
   *
   * @param source the Node from which the result should be imported
   * @return the imported result
   * @throws ImportException if an error occurs while importing
   */
  @Override
  public VerificationResult doImportFromXmlNode(Node source) throws ImportException {
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
      Message importedMessage = (Message) jaxbUnmarshaller.unmarshal(source);
      return makeVerificationResult(source, importedMessage);
    } catch (JAXBException exception) {
      throw new ImportException(exception);
    }
  }

  /**
   * Builds a {@link VerificationResult} from a GeTeTa {@link Message}.
   *
   * @param source the original top-level XML node of the verification result
   * @param importedMessage the JAXB-converted GeTeTa {@link Message} object
   * @return the imported result
   * @throws ImportException if an error occurs while importing
   */
  private VerificationResult makeVerificationResult(Node source, Message importedMessage)
      throws ImportException {
    try {
      /* Write log to file */
      File logFile = File.createTempFile("log-verification-", ".xml");
      TransformerFactory transformerFactory = TransformerFactory.newInstance();
      Transformer transformer = transformerFactory.newTransformer();
      DOMSource domSource = new DOMSource(source);
      StreamResult result = new StreamResult(logFile);
      transformer.transform(domSource, result);

      /* Return appropriate VerificationResult */
      switch (importedMessage.getReturncode()) {
        case RETURN_CODE_SUCCESS:
          return new VerificationSuccess(logFile);
        case RETURN_CODE_NOT_VERIFIED:
          return new edu.kit.iti.formal.stvs.model.verification.Counterexample(
              parseCounterexample(importedMessage), logFile);
        default:
          return new VerificationError(VerificationError.Reason.ERROR, logFile);
      }
    } catch (TransformerException | IOException exception) {
      throw new ImportException(exception);
    }
  }

  /**
   * Generates a counterexample from a given {@link Message} from the GeTeTa verification engine.
   *
   * @param message Message from the GeTeTa verification engine
   * @return concrete specification that represents the counterexample
   * @throws ImportException exception while importing
   */
  private ConcreteSpecification parseCounterexample(Message message) throws ImportException {
    // Parse variables from counterexample

    Map<String, Type> varTypes = new HashMap<>();
    List<String> varNames = new ArrayList<>();
    Map<String, VariableCategory> varCategories = new HashMap<>();

    for (SpecIoVariable specIoVariable : constraintSpecification.getColumnHeaders()) {
      String name = specIoVariable.getName();
      varNames.add(name);
      varCategories.put(name, specIoVariable.getCategory());
      varTypes.put(name, getType(specIoVariable));
    }

    List<String> rowMap = message.getCounterexample().getRowMappings().getRowMap();
    // It does not matter which of the rowMaps to use, so always use the zeroeth
      //take the last counterexample
    List<Integer> rowNums = parseRowMap(rowMap.get(rowMap.size()-1));
    Map<String, Value> currentValues = makeInitialValues(varTypes);

    // Parse concrete rows
    List<Counterexample.Step> steps = message.getCounterexample().getTrace().getStep();
    List<SpecificationRow<ConcreteCell>> concreteRows =
        makeConcreteRows(steps, rowNums, varNames, varTypes, currentValues, varCategories);

    // Parse durations
    List<ConcreteDuration> concreteDurations = makeConcreteDurations(rowNums);

    ConcreteSpecification concreteSpec = new ConcreteSpecification(true);
    for (String varName : varNames) {
      concreteSpec.getColumnHeaders()
          .add(new ValidIoVariable(varCategories.get(varName), varName, varTypes.get(varName)));
    }
    concreteSpec.getRows().addAll(concreteRows);
    concreteSpec.getDurations().addAll(concreteDurations);
    return concreteSpec;
  }

  private Map<String, Value> makeInitialValues(Map<String, Type> variableTypes) {
    Map<String, Value> initialValues = new HashMap<>();
    for (Map.Entry<String, Type> typeEntry : variableTypes.entrySet()) {
      initialValues.put(typeEntry.getKey(), typeEntry.getValue().generateDefaultValue());
    }
    return initialValues;
  }

  private Type getType(SpecIoVariable variable) throws ImportException {
    for (Type type : typeContext) {
      if (type.getTypeName().equals(variable.getType())) {
        return type;
      }
    }
    throw new ImportException("Cannot find type for variable " + variable.getName());
  }

  /**
   * Generates a list of concrete specification rows for a given list of
   * {@link edu.kit.iti.formal.exteta_1_0.report.Counterexample.Step}s.
   *
   * @param steps the GeTeTa output {
   * @link edu.kit.iti.formal.exteta_1_0.report.Counterexample.Step}s to import the rows from
   * @param rowNums the row mapping (map from cycle number to row number)
   * @param varNames the names of all declared free and i/o variables
   * @param varTypes the types of the variables
   * @param currentValues the current values of the variables
   * @param varCategories the categories (input/output) of the i/o variables
   * @return a list containing the rows of the counterexample
   * @throws ImportException if an error occurs during importing
   */
  private List<SpecificationRow<ConcreteCell>> makeConcreteRows(List<Counterexample.Step> steps,
      List<Integer> rowNums, List<String> varNames, Map<String, Type> varTypes,
      Map<String, Value> currentValues, Map<String, VariableCategory> varCategories)
      throws ImportException {
    List<SpecificationRow<ConcreteCell>> concreteRows = new ArrayList<>();
    int cycleNum = -1;
    // iterate over steps to create specification rows
    for (int i = 0; i < steps.size(); i++) {
      if (i - 1 > rowNums.size()) {
        break; // Make sure I terminate after right # of cycles
      }
      Counterexample.Step step = steps.get(i);
      processOutputVariables(varTypes, currentValues, varCategories, step);

      // Now can make and add the row
      if (cycleNum > -1) {
        SpecificationRow<ConcreteCell> row =
            makeSpecificationRowFromValues(varNames, currentValues);
        concreteRows.add(row);
      }

      processInputVariables(varTypes, currentValues, varCategories, step);
      cycleNum++;
    }
    return concreteRows;
  }

  /**
   * Converts a list of beginning cycles of durations into a List of {@link ConcreteDuration}s.
   *
   * @param rowNums list of beginning cycles of durations
   * @return list of durations
   */
  private List<ConcreteDuration> makeConcreteDurations(List<Integer> rowNums) {
    List<ConcreteDuration> concreteDurations = new ArrayList<>();
    int currentDuration = 0;
    int oldRowNum = 1;
    int cycle = 0;
    while (cycle < rowNums.size()) {
      int rowNum = rowNums.get(cycle);
      if (rowNum != oldRowNum) {
        concreteDurations.add(new ConcreteDuration(cycle - currentDuration, currentDuration));
        oldRowNum = rowNum;
        currentDuration = 0;
      }
      currentDuration++;
      cycle++;
    }
    concreteDurations.add(new ConcreteDuration(cycle - currentDuration, currentDuration));
    return concreteDurations;
  }

  /**
   * Parses the input variables of one {@link Counterexample.Step} and adds found types, values and
   * categories to the corresponding map.
   *
   * @param varTypes map of types
   * @param currentValues map of values for one step
   * @param varCategories map of categories
   * @param step current step
   * @throws ImportException exception while importing
   */
  private void processInputVariables(Map<String, Type> varTypes, Map<String, Value> currentValues,
      Map<String, VariableCategory> varCategories, Counterexample.Step step)
      throws ImportException {
    for (Assignment input : step.getInput()) { // Input vars are initialized here FOR THE NEXT
      // CYCLE
      String varName = VariableEscaper.unescapeIdentifier(input.getName());
      if (INPUT_VARIABLE_PATTERN.matcher(varName).matches()) {
        varCategories.put(varName, VariableCategory.INPUT);
        processVarAssignment(currentValues, varTypes, varName,
            VariableEscaper.unescapeIdentifier(input.getValue()));
      }
    }
  }

  /**
   * Parses the output variables of one {@link Counterexample.Step} and adds found types, values and
   * categories to the corresponding map.
   *
   * @param varTypes map of types
   * @param currentValues map of values for one step
   * @param varCategories map of categories
   * @param step current step
   * @throws ImportException exception while importing
   */
  private void processOutputVariables(Map<String, Type> varTypes, Map<String, Value> currentValues,
      Map<String, VariableCategory> varCategories, Counterexample.Step step)
      throws ImportException {
    for (Assignment state : step.getState()) { // Output vars are initialized here
      String stateString = state.getName().trim();
      if (CODE_VARIABLE_PATTERN.matcher(stateString).matches()) {
        int periodIndex = stateString.indexOf(".");
        String varName = VariableEscaper
            .unescapeIdentifier(stateString.substring(periodIndex + 1, stateString.length()));
        varCategories.put(varName, VariableCategory.OUTPUT);
        String varValue = VariableEscaper.unescapeIdentifier(state.getValue());
        processVarAssignment(currentValues, varTypes, varName, varValue);
      }
    }
  }

  /**
   * Creates a {@link SpecificationRow} for one step.
   *
   * @param varNames variable names
   * @param currentValues values for one step
   * @return specification row representing one step
   */
  private SpecificationRow<ConcreteCell> makeSpecificationRowFromValues(List<String> varNames,
      Map<String, Value> currentValues) {
    SpecificationRow<ConcreteCell> row = SpecificationRow.createUnobservableRow(new HashMap<>());
    for (String varName : varNames) {
      row.getCells().put(varName, new ConcreteCell(currentValues.get(varName)));
    }
    return row;
  }

  /**
   * Parses a list of integers separated by a comma and space.
   *
   * @param rowMapString string to be parsed
   * @return list of integers
   */
  private List<Integer> parseRowMap(String rowMapString) {
    String[] tokens = rowMapString.trim().split(", ");
    List<Integer> res = new ArrayList<>();
    for (String token : tokens) {
      res.add(Integer.parseInt(token));
    }
    return res;
  }

  @Override
  protected URL getXsdResource() throws IOException {
    return this.getClass().getResource("/fileFormats/report.xsd");
  }

  /**
   * Processes an assignment of a single value represented by {@code varValue} to a variable
   * specified by {@code varName} for one step in the counterexample. The type of the value is
   * determined by matching {@code varValue} against several regular expressions and, in case of an
   * enum type, further information is taken from {@code typeContext}. The value is then added to
   * the {@code currentValues}-Map as a {@link Value}. Found types are added to {@code varTypes}.
   *
   * @param currentValues Represents the values of variables for a step
   * @param varTypes Map of types
   * @param varName Name of the variable
   * @param varValue String representation of this variable for one step
   * @throws ImportException when an enum literal is assigned to a variable of incompatible enum
   *         type
   */
  private void processVarAssignment(Map<String, Value> currentValues, Map<String, Type> varTypes,
      String varName, String varValue) throws ImportException {
    if (INT_VALUE_PATTERN.matcher(varValue).matches()) {
      int underlineIndex = varValue.indexOf("_");
      int intVal = Integer.parseInt(varValue.substring(underlineIndex + 1, varValue.length()));
      currentValues.put(varName, new ValueInt(intVal));
      if (!varTypes.containsKey(varName)) {
        varTypes.put(varName, TypeInt.INT);
      }
    } else if (BOOL_VALUE_PATTERN.matcher(varValue).matches()) {
      if (!varTypes.containsKey(varName)) {
        varTypes.put(varName, TypeBool.BOOL);
      }
      if (varValue.equals("TRUE")) {
        currentValues.put(varName, ValueBool.TRUE);
      } else {
        currentValues.put(varName, ValueBool.FALSE);
      }
    } else {
      if (!varTypes.containsKey(varName)) {
        // Find the enum type for this variable
        boolean enumTypeFound = false;
        for (Type type : typeContext) {
          Optional<Value> val = type.parseLiteral(varValue);
          if (val.isPresent()) {
            enumTypeFound = true;
            varTypes.put(varName, type);
          }
        }
        if (!enumTypeFound) {
          throw new ImportException("No enum type found for literal " + varValue);
        }
      }
      Optional<Value> enumVal = varTypes.get(varName).parseLiteral(varValue);
      if (!enumVal.isPresent()) {
        throw new ImportException("Illegal literal " + varValue + " for enum type "
            + varTypes.get(varName).getTypeName());
      }
      currentValues.put(varName, enumVal.get());
    }
  }
}

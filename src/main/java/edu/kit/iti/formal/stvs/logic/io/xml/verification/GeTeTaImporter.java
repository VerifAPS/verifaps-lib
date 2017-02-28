package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.exteta_1_0.report.Assignment;
import edu.kit.iti.formal.exteta_1_0.report.Counterexample;
import edu.kit.iti.formal.exteta_1_0.report.Message;
import edu.kit.iti.formal.exteta_1_0.report.ObjectFactory;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.VariableEscaper;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlImporter;
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
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.model.verification.VerificationError;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;

import java.io.File;
import java.io.IOException;
import java.net.URISyntaxException;
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
 * Provides the functionality to import the output of the GeTeTa verification engine.
 *
 * @author Benjamin Alt
 */
public class GeTeTaImporter extends XmlImporter<VerificationResult> {

  /* GeTeTa return codes */
  private static final String RETURN_CODE_SUCCESS = "verified";
  private static final String RETURN_CODE_NOT_VERIFIED = "not-verified";
  private static final String RETURN_CODE_FATAL = "fatal-error";
  private static final String RETURN_CODE_ERROR = "error";

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

  /**
   * Creates a new Importer for results after verification.
   *
   * @param typeContext List of types available in the specification
   */
  public GeTeTaImporter(List<Type> typeContext) {
    this.typeContext = typeContext;
  }

  /**
   * Imports a {@link VerificationResult} from {@link Node}.
   *
   * @param source the Node from which the result should be imported
   * @return the imported result
   * @throws ImportException Exception while importing
   */
  @Override
  public VerificationResult doImportFromXmlNode(Node source) throws ImportException {
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
      Message importedMessage = (Message) jaxbUnmarshaller.unmarshal(source);
      return makeVerificationResult(source, importedMessage);
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  /**
   * Builds a {@link VerificationResult} from {@link Node}.
   *
   * @param source the Node from which the result should be imported
   * @param importedMessage return message from the verification engine
   * @return the imported result
   * @throws ImportException Exception while importing
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
      String logFilePath = logFile.getAbsolutePath();
      switch (importedMessage.getReturncode()) {
        case RETURN_CODE_SUCCESS:
          return new VerificationResult(VerificationResult.Status.VERIFIED, logFile, null);
        case RETURN_CODE_NOT_VERIFIED:
          return new VerificationResult(parseCounterexample(importedMessage), logFile);
        default:
          VerificationError error = new VerificationError(VerificationError.Reason.ERROR);
          return new VerificationResult(VerificationResult.Status.ERROR, logFile, error);
      }
    } catch (TransformerException | IOException e) {
      throw new ImportException(e);
    }
  }

  /**
   * Generates a counterexample from a given message from the GeTeTa verification engine.
   *
   * @param message Message from the GeTeTa verification engine
   * @return concrete specification that represents the counterexample
   * @throws ImportException exception while importing
   */
  private ConcreteSpecification parseCounterexample(Message message) throws ImportException {
    List<SpecificationRow<ConcreteCell>> concreteRows = new ArrayList<>();

    // Parse variables from counterexample
    Message.Log log = message.getLog();
    // Don't know exact enum types yet --> Map from name to either "INT", "BOOLEAN", "ENUM"
    // Don't know whether input or output yet
    Map<String, Type> varTypes = new HashMap<>();
    List<String> varNames = getVarNamesFromLog(log);

    // Parse rows & durations
    int currentDurationCount = 1;
    int lastRowNum = -1;
    List<Counterexample.Step> steps = message.getCounterexample().getTrace().getStep();
    List<String> rowMap = message.getCounterexample().getRowMappings().getRowMap();
    List<Integer> rowNums = parseRowMap(rowMap.get(0));
    Map<String, Value> currentValues = new HashMap<>();
    Map<String, VariableCategory> varCategories = new HashMap<>();
    int cycleNum = -1;
    // iterate over steps to create specification rows
    for (int i = 0; i < steps.size(); i++) {
      if (i - 1 > rowNums.size()) {
        break; // Make sure I terminate after right # of cycles
      }
      Counterexample.Step step = steps.get(i);
      processOutputVariables(varTypes, currentValues, varCategories, step);

      // Now I can make and add the row
      if (cycleNum > -1) {
        SpecificationRow<ConcreteCell> row =
            makeSpecificationRowFromValues(varNames, currentValues);
        concreteRows.add(row);
      }

      processInputVariables(varTypes, currentValues, varCategories, step);
      cycleNum++;
    }

    // Parse durations
    List<ConcreteDuration> concreteDurations = makeConcreteDuration(rowNums);

    ConcreteSpecification concreteSpec = new ConcreteSpecification(true);
    for (String varName : varNames) {
      if (currentValues.containsKey(varName)) {
        concreteSpec.getColumnHeaders()
            .add(new ValidIoVariable(varCategories.get(varName), varName, varTypes.get(varName)));
      }
    }
    concreteSpec.getRows().addAll(concreteRows);
    concreteSpec.getDurations().addAll(concreteDurations);
    return concreteSpec;
  }

  /**
   * Converts a list of beginning cycles of durations into a List of {@link ConcreteDuration}.
   *
   * @param rowNums list of beginning cycles of durations
   * @return list of durations
   */
  private List<ConcreteDuration> makeConcreteDuration(List<Integer> rowNums) {
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
      String varName = VariableEscaper.unescapeName(input.getName());
      if (INPUT_VARIABLE_PATTERN.matcher(varName).matches()) {
        varCategories.put(varName, VariableCategory.INPUT);
        processVarAssignment(currentValues, varTypes, varName,
            VariableEscaper.unescapeName(input.getValue()));
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
            .unescapeName(stateString.substring(periodIndex + 1, stateString.length()));
        varCategories.put(varName, VariableCategory.OUTPUT);
        String varValue = VariableEscaper.unescapeName(state.getValue());
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
      if (currentValues.containsKey(varName)) {
        row.getCells().put(varName, new ConcreteCell(currentValues.get(varName)));
      }
    }
    return row;
  }

  /**
   * Parses the output log of the GeTeTa verification engine and returns all found variable names.
   *
   * @param log GeTeTa output log
   * @return list of variable names
   */
  private List<String> getVarNamesFromLog(Message.Log log) {
    List<Message.Log.Entry> entries = log.getEntry();
    List<String> varNames = new ArrayList<>();

    for (int i = 0; i < entries.size(); i++) {
      Message.Log.Entry entry = entries.get(i);
      if (VARIABLES_FOUND_PATTERN.matcher(entry.getValue()).matches()) {
        Message.Log.Entry nextEntry = entries.get(++i);
        String entryString = nextEntry.getValue();
        while (VARIABLE_DECL_PATTERN.matcher(entryString).matches()) {
          entryString = entryString.replaceAll("\\s+", "");
          int colonIndex = entryString.indexOf(":");
          String varName = entryString.substring(0, colonIndex);
          varNames.add(VariableEscaper.unescapeName(varName));
          entryString = entries.get(++i).getValue();
        }
        break;
      }
    }
    return varNames;
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
  protected String getXsdFilePath() throws URISyntaxException {
    File xsdFile = new File(this.getClass().getResource("/fileFormats/report.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }

  /**
   * Processes an assignment of a single value represented by {@code varValue} to a variable
   * specified by {@code varName} for one step in the counterexample. The type of the value is
   * determined by matching {@code varValue} against several regular expressions and,in case of an
   * enum type, further information is taken from {@code typeContext}. The value is then added to
   * the {@code currentValues}-Map as a {@link Value}. Found types are added to {@code varTypes}.
   *
   * @param currentValues Represents the values of variables for a step
   * @param varTypes Map of types
   * @param varName Name of the variable
   * @param varValue String representation of theís variable for one step
   * @throws ImportException Illegal literal for enum
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

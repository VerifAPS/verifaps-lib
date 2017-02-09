package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.exteta_1_0.report.Assignment;
import edu.kit.iti.formal.exteta_1_0.report.Counterexample;
import edu.kit.iti.formal.exteta_1_0.report.Message;
import edu.kit.iti.formal.exteta_1_0.report.ObjectFactory;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlImporter;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import edu.kit.iti.formal.stvs.model.verification.VerificationResult;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.net.URISyntaxException;
import java.util.*;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * @author Benjamin Alt
 */
public class GeTeTaImporter extends XmlImporter<VerificationResult> {

  private final static String RETURN_CODE_SUCCESS = "verified";
  private final static String RETURN_CODE_NOT_VERIFIED = "counterexample";
  private final static String IDENTIFIER_RE = "[$a-zA-Z0-9_]+";
  private final static Pattern VARIABLES_FOUND_PATTERN = Pattern.compile("[0-9]+ variables " +
      "found");
  private final static Pattern VARIABLE_DECL_PATTERN = Pattern.compile("\\s*" + IDENTIFIER_RE +
      " : " + IDENTIFIER_RE);
  private final static Pattern CODE_VARIABLE_PATTERN = Pattern.compile("code\\." + IDENTIFIER_RE);
  private final static Pattern INT_VALUE_PATTERN = Pattern.compile("0sd16_-?[0-9]+");
  private final static Pattern BOOL_VALUE_PATTERN = Pattern.compile("(TRUE)|(FALSE)");
  private final List<Type> typeContext;

  public GeTeTaImporter(List<Type> typeContext) {
    this.typeContext = typeContext;
  }

  @Override
  public VerificationResult doImportFromXmlNode(Node source) throws ImportException {
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      Unmarshaller jaxbUnmarshaller = jaxbContext.createUnmarshaller();
      Message importedMessage = (Message) jaxbUnmarshaller.unmarshal(source);
      if (importedMessage.getReturncode().equals(RETURN_CODE_SUCCESS)) {
        return new VerificationResult();
      } else if (importedMessage.getReturncode().equals(RETURN_CODE_NOT_VERIFIED)) {
        return new VerificationResult(parseCounterexample(importedMessage));
      } else {
        throw new ImportException("There was an error in the GeTeTa verification engine");
      }
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  private ConcreteSpecification parseCounterexample(Message message) throws ImportException {
    List<SpecIoVariable> ioVariables = new ArrayList<>();
    List<SpecificationRow<ConcreteCell>> concreteRows = new ArrayList<>();
    List<ConcreteDuration> concreteDurations = new ArrayList<>();

    // Parse variables from counterexample
    Message.Log log = message.getLog();
    // Don't know exact enum types yet --> Map from name to either "INT", "BOOLEAN", "ENUM"
    // Don't know whether input or output yet
    Map<String, Type> varTypes = new HashMap<>();
    List<Message.Log.Entry> entries = log.getEntry();
    List<String> varNames = new ArrayList<>();

    for (int i = 0; i < entries.size(); i++) {
      Message.Log.Entry entry = entries.get(i);
      if (VARIABLES_FOUND_PATTERN.matcher(entry.getValue()).matches()) {
        Message.Log.Entry nextEntry = entries.get(++i);
        String entryString = nextEntry.getValue();
        while(VARIABLE_DECL_PATTERN.matcher(entryString).matches()) {
          entryString = entryString.replaceAll("\\s+", "");
          int colonIndex = entryString.indexOf(":");
          String varName = entryString.substring(0, colonIndex);
          varNames.add(varName);
          entryString = entries.get(++i).getValue();
        }
        break;
      }
    }

    // Parse rows & durations
    int currentDurationCount = 1;
    int lastRowNum = -1;
    List<Counterexample.Step> steps = message.getCounterexample().getStep();
    Map<String, Value> currentValues = new HashMap<>();
    Map<String, VariableCategory> varCategories = new HashMap<>();
    for (Counterexample.Step step : steps) {
      int rowNum = step.getRow();
      for (Assignment state : step.getState()) { // Output vars are initialized here
        String stateString = state.getName().trim();
        if (CODE_VARIABLE_PATTERN.matcher(stateString).matches()) {
          int periodIndex = stateString.indexOf(".");
          String varName = stateString.substring(periodIndex + 1, stateString.length());
          varCategories.put(varName, VariableCategory.OUTPUT);
          String varValue = state.getValue();
          processVarAssignment(currentValues, varTypes, varName, varValue);
        }
      }

      for (Assignment input : step.getInput()) {
        String varName = input.getName();
        varCategories.put(varName, VariableCategory.INPUT);
        processVarAssignment(currentValues, varTypes, input.getName(), input.getValue());
      }

      // Now I can make and add the row!
      if (step.getState().size() > 0) {
        if (rowNum > -1 && rowNum <= concreteRows.size()) {
          SpecificationRow<ConcreteCell> row = new SpecificationRow<>(new HashMap<>());
          if (rowNum < concreteRows.size()) {
            row = concreteRows.get(rowNum);
          }
          for (String varName : currentValues.keySet()) {
            row.getCells().put(varName, new ConcreteCell(currentValues.get(varName)));
          }
          concreteRows.add(rowNum, row);
        } else if (rowNum != -1) {
          throw new ImportException("Illegal row number: " + rowNum);
        }
      }

      if (rowNum > -1) {
        if (step.getState().size() > 0) { // Only steps with "state" influence durations
          if (lastRowNum != rowNum) {
            // Started new row --> make and add new duration
            concreteDurations.add(new ConcreteDuration(rowNum, currentDurationCount));
            currentDurationCount = 1;
            lastRowNum = rowNum;
          } else {
            currentDurationCount++;
          }
        }
      }
    }
    return new ConcreteSpecification(concreteRows, concreteDurations, true);
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    File xsdFile = new File
        (this.getClass().getResource("/fileFormats/report.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }

  private void processVarAssignment(Map<String,Value> currentValues, Map<String,Type> varTypes,
                                  String varName,
                    String varValue) throws ImportException {
    if (INT_VALUE_PATTERN.matcher(varValue).matches()) {
      int underlineIndex = varValue.indexOf("_");
      int intVal = Integer.parseInt(varValue.substring(underlineIndex + 1, varValue.length
          ()));
      currentValues.put(varName, new ValueInt(intVal));
      if (!varTypes.containsKey(varName)) varTypes.put(varName, TypeInt.INT);
    } else if (BOOL_VALUE_PATTERN.matcher(varValue).matches()) {
      if (!varTypes.containsKey(varName)) varTypes.put(varName, TypeBool.BOOL);
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
        throw new ImportException("Illegal literal " + varValue + "for enum type " +
            varTypes.get(varName).getTypeName());
      }
      currentValues.put(varName, enumVal.get());
    }
  }

  public static void main(String[] args) throws ImportException, FileNotFoundException {
    List<Type> typeContext = Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    GeTeTaImporter importer = new GeTeTaImporter(typeContext);
    VerificationResult result = importer.doImport(new FileInputStream
        ("/home/bal/Projects/kit/pse/stverificationstudio/src/test/resources/edu/kit/iti/formal" +
            "/stvs/logic/io/xml/report_counterexample_1.xml"));
    System.out.println();
  }
}

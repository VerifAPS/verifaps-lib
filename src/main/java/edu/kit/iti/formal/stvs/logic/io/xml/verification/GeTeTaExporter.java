package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.exteta_1.*;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.VariableEscaper;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlExporter;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBElement;
import java.util.List;


/**
 * Exporter for communication with the GeTeTa.
 *
 * @author Benjamin Alt
 */
public class GeTeTaExporter extends XmlExporter<ConstraintSpecification> {
  private ObjectFactory objectFactory;

  public GeTeTaExporter() {
    objectFactory = new ObjectFactory();
  }

  /**
   * Creates {@link Steps} that correspond to the rows in the given {@link ConstraintSpecification}.
   *
   * @param source The specification from which the steps should be taken
   * @return Steps object ready to be used in a {@link TestTable}
   */
  private Steps makeSteps(ConstraintSpecification source) {
    Steps steps = objectFactory.createSteps();
    // A step corresponds to a row in a ConstraintSpecification
    List<SpecificationRow<ConstraintCell>> rows = source.getRows();
    List<ConstraintDuration> durations = source.getDurations();
    for (int i = 0; i < rows.size(); i++) {
      SpecificationRow<ConstraintCell> row = rows.get(i);
      Step step = objectFactory.createStep();
      step.setDuration(durations.get(i).getAsString());
      for (SpecIoVariable specIoVariable : source.getColumnHeaders()) {
        String variable = specIoVariable.getName();
        ConstraintCell cell = row.getCells().get(variable);
        step.getCell().add(VariableEscaper.escapeCellExpression(cell.getAsString()));
      }
      steps.getBlockOrStep().add(step);
    }
    return steps;
  }

  /**
   * Creates {@link Variables} from all variables present in the given
   * {@link ConstraintSpecification}.
   *
   * @param source The specification from which the variables should be taken
   * @return Variables object ready to be used in a {@link TestTable}
   */
  private Variables makeVariables(ConstraintSpecification source) {
    Variables variables = objectFactory.createVariables();
    variables.getVariableOrConstraint().addAll(makeIoVariables(source).getVariableOrConstraint());
    variables.getVariableOrConstraint().addAll(makeFreeVariables(source).getVariableOrConstraint());
    return variables;
  }

  /**
   * Creates {@link Variables} from the {@link FreeVariable FreeVariables}
   * present in the given {@link ConstraintSpecification}.
   *
   * @param source The specification from which the variables should be taken
   * @return Variables object
   */
  private Variables makeFreeVariables(ConstraintSpecification source) {
    Variables variables = objectFactory.createVariables();
    for (FreeVariable freeVariable : source.getFreeVariableList().getVariables()) {
      ConstraintVariable exportedVariable = objectFactory.createConstraintVariable();
      exportedVariable.setName(VariableEscaper.escapeName(freeVariable.getName()));
      exportedVariable.setDataType(getDataType(freeVariable));
      if (freeVariable.getDefaultValue().length() > 0) {
        exportedVariable.setConstraint(VariableEscaper.escapeName(freeVariable.getDefaultValue()));
      } else {
        exportedVariable.setConstraint("-");
      }
      variables.getVariableOrConstraint().add(exportedVariable);
    }
    return variables;
  }

  /**
   * Creates {@link Variables} from the {@link SpecIoVariable} present
   * in the given {@link ConstraintSpecification}.
   *
   * @param source The specification from which the variables should be taken
   * @return Variables object
   */
  private Variables makeIoVariables(ConstraintSpecification source) {
    Variables variables = objectFactory.createVariables();
    for (SpecIoVariable ioVariable : source.getColumnHeaders()) {
      IoVariable exportedVariable = objectFactory.createIoVariable();
      exportedVariable.setName(VariableEscaper.escapeName(ioVariable.getName()));
      exportedVariable.setDataType(getDataType(ioVariable));
      if (ioVariable.getCategory() == VariableCategory.INPUT) {
        exportedVariable.setIo("input");
      } else {
        exportedVariable.setIo("output");
      }
      variables.getVariableOrConstraint().add(exportedVariable);
    }
    return variables;
  }

  /**
   * Get {@link DataType} of a variable from STVS.
   *
   * @param variable Variable from which the @link DataType} should be determined
   * @return the determined @link DataType} of the {@code variable}
   */
  private DataType getDataType(edu.kit.iti.formal.stvs.model.common.Variable variable) {
    if (variable.getType().equals("INT")) {
      return DataType.INT;
    } else if (variable.getType().equals("BOOL")) {
      return DataType.BOOLEAN;
    } else {
      return DataType.ENUM;
    }
  }

  /**
   * Converts a given {@link ConstraintSpecification} into a XML node
   * that is compatible with the GeTeTa verification engine.
   *
   * @param source The specification that shoul be converted
   * @return XML Node representing the specification
   * @throws ExportException marshalling was not successful
   */
  @Override
  public Node exportToXmlNode(ConstraintSpecification source) throws ExportException {
    TestTable testTable = objectFactory.createTestTable();
    testTable.setVariables(makeVariables(source));
    testTable.setSteps(makeSteps(source));
    JAXBElement<TestTable> element = objectFactory.createTestTable(testTable);
    return marshalToNode(element, "edu.kit.iti.formal.exteta_1");
  }
}

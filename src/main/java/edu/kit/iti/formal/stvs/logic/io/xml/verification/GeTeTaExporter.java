package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.exteta_1.ConstraintVariable;
import edu.kit.iti.formal.exteta_1.DataType;
import edu.kit.iti.formal.exteta_1.IoVariable;
import edu.kit.iti.formal.exteta_1.ObjectFactory;
import edu.kit.iti.formal.exteta_1.Step;
import edu.kit.iti.formal.exteta_1.Steps;
import edu.kit.iti.formal.exteta_1.TestTable;
import edu.kit.iti.formal.exteta_1.Variables;
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

import java.util.List;
import javax.xml.bind.JAXBElement;

import org.w3c.dom.Node;

/**
 * Exporter for communication with the GeTeTa verification engine. Provides functionality for
 * converting {@link ConstraintSpecification}s into an XML format compatible with the GeTeTa
 * input format.
 *
 * @author Benjamin Alt
 */
public class GeTeTaExporter extends XmlExporter<ConstraintSpecification> {
  private static final String EXTETA_NAMESPACE = "edu.kit.iti.formal.exteta_1";
  private ObjectFactory objectFactory;

  public GeTeTaExporter() {
    objectFactory = new ObjectFactory();
  }

  /**
   * Creates {@link Steps} that correspond to the rows in the given {@link ConstraintSpecification}.
   *
   * @param source The specification for which the steps should be generated
   * @return Steps object (to be inserted into a {@link TestTable})
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
   * Creates {@link Variables} from all free and i/o variables present in the given
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
   * Creates {@link Variables} from the {@link FreeVariable FreeVariables} present in the given
   * {@link ConstraintSpecification}.
   *
   * @param source The specification from which the variables should be generated
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
   * Creates {@link Variables} from the {@link SpecIoVariable} present in the given
   * {@link ConstraintSpecification}.
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
   * Create the {@link DataType} for a given variable.
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
   * Converts a given {@link ConstraintSpecification} into an XML node that conforms to the
   * GeTeTa verification engine input format.
   *
   * @param source The specification that should be converted
   * @return XML Node representing the specification
   * @throws ExportException if marshalling was not successful
   */
  @Override
  public Node exportToXmlNode(ConstraintSpecification source) throws ExportException {
    TestTable testTable = objectFactory.createTestTable();
    testTable.setVariables(makeVariables(source));
    testTable.setSteps(makeSteps(source));
    JAXBElement<TestTable> element = objectFactory.createTestTable(testTable);
    return marshalToNode(element, EXTETA_NAMESPACE);
  }
}

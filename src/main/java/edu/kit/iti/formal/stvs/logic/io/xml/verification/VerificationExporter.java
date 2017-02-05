package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import edu.kit.iti.formal.exteta_1.*;
import edu.kit.iti.formal.exteta_1.IoVariable;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.xml.Config;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlExporter;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlSpecExporter;
import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.table.*;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBElement;
import java.util.List;

/**
 * @author Benjamin Alt
 */
public class VerificationExporter extends XmlExporter<ConstraintSpecification> {

  private final String DEFAULT_CONSTRAINT = "[-,-]"; // TODO Ask Mr. Weigl: Syntax for no constraint
  private ObjectFactory objectFactory;

  public VerificationExporter() {
    objectFactory = new ObjectFactory();
  }

  @Override
  public Node exportToXmlNode(ConstraintSpecification source) throws ExportException {
    TestTable testTable = objectFactory.createTestTable();
    testTable.setVariables(makeVariables(source));
    testTable.setSteps(makeSteps(source));
    JAXBElement<TestTable> element = objectFactory.createTestTable(testTable);
    return marshalToNode(element);
  }

  private Steps makeSteps(ConstraintSpecification source) {
    Steps steps = objectFactory.createSteps();
    // A step corresponds to a row in a ConstraintSpecification
    List<SpecificationRow<ConstraintCell>> rows = source.getRows();
    List<ConstraintDuration> durations = source.getDurations();
    for (int i = 0; i < rows.size(); i++) {
      SpecificationRow<ConstraintCell> row = rows.get(i);
      Step step = objectFactory.createStep();
      step.setDuration(durations.get(i).getAsString());
      for (SpecificationColumn<ConstraintCell> col : source.getColumns()) {
        String variable = col.getSpecIoVariable().getName();
        ConstraintCell cell = row.getCells().get(variable);
        step.getCell().add(cell.getAsString());
      }
      steps.getBlockOrStep().add(step);
    }
    return steps;
  }

  private Variables makeVariables(ConstraintSpecification source) {
    Variables variables = objectFactory.createVariables();
    for (SpecificationColumn<ConstraintCell> col : source.getColumns()) {
      IoVariable exportedVariable = objectFactory.createIoVariable();
      SpecIoVariable ioVariable = col.getSpecIoVariable();
      exportedVariable.setName(ioVariable.getName());
      exportedVariable.setDataType(getDataType(ioVariable));
      if (ioVariable.getCategory() == VariableCategory.INPUT) {
        exportedVariable.setIo("input");
      } else {
        exportedVariable.setIo("output");
      }
      variables.getVariableOrConstraint().add(exportedVariable);
    }
    for (FreeVariable freeVariable : source.getFreeVariableSet().getVariableSet()) {
      ConstraintVariable exportedVariable = objectFactory.createConstraintVariable();
      exportedVariable.setName(freeVariable.getName());
      exportedVariable.setDataType(getDataType(freeVariable));
      exportedVariable.setConstraint(DEFAULT_CONSTRAINT);
      variables.getVariableOrConstraint().add(exportedVariable);
    }
    return variables;
  }

  private DataType getDataType(edu.kit.iti.formal.stvs.model.common.Variable variable) {
    if (variable.getType().getTypeName().equals("INT")) {
      return DataType.INT;
    } else if (variable.getType().getTypeName().equals("BOOL")) {
      return DataType.BOOLEAN;
    } else {
      return DataType.ENUM;
    }
  }
}

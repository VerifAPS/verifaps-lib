package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import com.sun.xml.bind.marshaller.DataWriter;
import edu.kit.iti.formal.exteta_1.*;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.Exporter;
import edu.kit.iti.formal.stvs.logic.io.VariableEscaper;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlExporter;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import org.w3c.dom.Document;
import org.w3c.dom.Node;

import java.io.*;
import java.util.ArrayList;
import java.util.List;
import java.util.regex.Matcher;
import java.util.regex.Pattern;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Marshaller;
import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;
import javax.xml.parsers.ParserConfigurationException;
import java.io.ByteArrayOutputStream;
import java.io.PrintWriter;
import java.io.StringWriter;
import java.util.List;


/**
 * Exporter for communication with the GeTeTa
 * @author Benjamin Alt
 */
public class GeTeTaExporter extends XmlExporter<ConstraintSpecification> {
  private ObjectFactory objectFactory;

  public GeTeTaExporter() {
    objectFactory = new ObjectFactory();
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
      for (SpecIoVariable specIoVariable : source.getColumnHeaders()) {
        String variable = specIoVariable.getName();
        ConstraintCell cell = row.getCells().get(variable);
        step.getCell().add(VariableEscaper.escapeCellExpression(cell.getAsString()));
      }
      steps.getBlockOrStep().add(step);
    }
    return steps;
  }

  private Variables makeVariables(ConstraintSpecification source) {
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
    for (FreeVariable freeVariable : source.getFreeVariableList().getVariables()) {
      ConstraintVariable exportedVariable = objectFactory.createConstraintVariable();
      exportedVariable.setName(VariableEscaper.escapeName(freeVariable.getName()));
      exportedVariable.setDataType(getDataType(freeVariable));
      exportedVariable.setConstraint(VariableEscaper.escapeName(freeVariable.getDefaultValue()));
      variables.getVariableOrConstraint().add(exportedVariable);
    }
    return variables;
  }

  private DataType getDataType(edu.kit.iti.formal.stvs.model.common.Variable variable) {
    if (variable.getType().equals("INT")) {
      return DataType.INT;
    } else if (variable.getType().equals("BOOL")) {
      return DataType.BOOLEAN;
    } else {
      return DataType.ENUM;
    }
  }

  @Override
  public Node exportToXmlNode(ConstraintSpecification source) throws ExportException {
    TestTable testTable = objectFactory.createTestTable();
    testTable.setVariables(makeVariables(source));
    testTable.setSteps(makeSteps(source));
    JAXBElement<TestTable> element = objectFactory.createTestTable(testTable);
    return marshalToNode(element, "edu.kit.iti.formal.exteta_1");
  }
}

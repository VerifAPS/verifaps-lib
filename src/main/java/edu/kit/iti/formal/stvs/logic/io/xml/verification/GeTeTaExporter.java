package edu.kit.iti.formal.stvs.logic.io.xml.verification;

import com.sun.xml.bind.marshaller.DataWriter;
import edu.kit.iti.formal.exteta_1.*;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.Exporter;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import org.w3c.dom.Document;

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
public class GeTeTaExporter implements Exporter<ConstraintSpecification> {

  private ObjectFactory objectFactory;

  public GeTeTaExporter() {
    objectFactory = new ObjectFactory();
  }

  public String exportToXmlString(ConstraintSpecification source) throws ExportException {
    TestTable testTable = objectFactory.createTestTable();
    testTable.setVariables(makeVariables(source));
    testTable.setSteps(makeSteps(source));
    JAXBElement<TestTable> element = objectFactory.createTestTable(testTable);
    return marshalToString(element);
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
        step.getCell().add(cell.getAsString());
      }
      steps.getBlockOrStep().add(step);
    }
    return steps;
  }

  private Variables makeVariables(ConstraintSpecification source) {
    Variables variables = objectFactory.createVariables();
    for (SpecIoVariable ioVariable : source.getColumnHeaders()) {
      IoVariable exportedVariable = objectFactory.createIoVariable();
      exportedVariable.setName(ioVariable.getName());
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
      exportedVariable.setName(freeVariable.getName());
      exportedVariable.setDataType(getDataType(freeVariable));
      exportedVariable.setConstraint(freeVariable.getDefaultValue());
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

  protected static String marshalToString(JAXBElement element) throws ExportException {
    try {
      DocumentBuilderFactory dbf = DocumentBuilderFactory.newInstance();
      DocumentBuilder db = dbf.newDocumentBuilder();
      Document document = db.newDocument();
      JAXBContext context = JAXBContext.newInstance("edu.kit.iti.formal.exteta_1");
      Marshaller marshaller = context.createMarshaller();
      marshaller.setProperty("jaxb.formatted.output", Boolean.TRUE);
      marshaller.setProperty(javax.xml.bind.Marshaller.JAXB_ENCODING, "utf-8");
      StringWriter stringWriter = new StringWriter();
      PrintWriter printWriter = new PrintWriter(stringWriter);
      DataWriter dataWriter = new DataWriter(printWriter, "UTF-8", new NoEscapeHandler());
      marshaller.marshal(element, dataWriter);
      return stringWriter.toString();
    } catch (ParserConfigurationException | JAXBException e) {
      throw new ExportException(e);
    }
  }

  @Override
  public ByteArrayOutputStream export(ConstraintSpecification source) throws ExportException {
    String res = exportToXmlString(source);
    byte[] bytes = res.getBytes();
    ByteArrayOutputStream baos = new ByteArrayOutputStream(bytes.length);
    baos.write(bytes, 0, bytes.length);
    return baos;
  }
}

package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableSet;
import edu.kit.iti.formal.stvs.model.common.IllegalValueTypeException;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;
import edu.kit.iti.formal.stvs.model.expressions.*;
import edu.kit.iti.formal.stvs.model.table.*;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import java.io.File;
import java.net.URISyntaxException;
import java.util.*;

import javafx.collections.FXCollections;
import org.w3c.dom.Node;

/**
 * @author Benjamin Alt
 */
public class XmlConcreteSpecImporter extends XmlImporter<ConcreteSpecification> {

  private Unmarshaller unmarshaller;
  private Set<Type> typeContext;
  private XmlConstraintSpecImporter constraintSpecImporter;

  public XmlConcreteSpecImporter() throws ImportException {
    constraintSpecImporter = new XmlConstraintSpecImporter();
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      unmarshaller = jaxbContext.createUnmarshaller();
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  public ConcreteSpecification doImportFromXmlNode(Node source) throws ImportException {
    try {
      SpecificationTable importedSpec = ((JAXBElement<SpecificationTable>) unmarshaller
          .unmarshal(source)).getValue();

      Set<Type> typeContext = constraintSpecImporter.importTypeContext(importedSpec.getEnumTypes());
      List<SpecIoVariable> ioVariables = constraintSpecImporter.importIoVariables(importedSpec
              .getVariables(), typeContext);
      return importConcreteSpec(typeContext, ioVariables, importedSpec);
    } catch (JAXBException  e) {
      throw new ImportException(e);
    }
  }

  private ConcreteSpecification importConcreteSpec(Set<Type> typeContext, List<SpecIoVariable>
      ioVariables, SpecificationTable importedSpec) throws
      ImportException {
    if (!importedSpec.isIsConcrete()) {
      throw new ImportException("Cannot import a ConcreteSpecification from a specification not " +
          "declared as concrete");
    }
    ConcreteSpecification concreteSpec = new ConcreteSpecification(importedSpec.isIsCounterExample());

    // Add the specIoVariables (column headers)
    for (SpecIoVariable specIoVariable : ioVariables) {
      concreteSpec.getSpecIoVariables().add(specIoVariable);
    }

    // Add the rows
    Rows rows = importedSpec.getRows();
    int currentCycle = 0;
    for (int i = 0; i < rows.getRow().size(); i++) {
      Rows.Row row = rows.getRow().get(i);
      int currentDuration = Integer.parseInt(row.getDuration().getValue());
      concreteSpec.getDurations().add(new ConcreteDuration(currentCycle, currentDuration));
      for (int j = 0; j < row.getCycle().size(); j++){
        Map<String,ConcreteCell> cellsMap = new HashMap<>();
        Rows.Row.Cycle cycle = row.getCycle().get(j);
        for (int k = 0; k < ioVariables.size(); k++) {
          String cell = cycle.getCell().get(k);
          Type cellType = ioVariables.get(k).getType();
          Optional<Value> val = cellType.parseLiteral(cell);
          if (val.isPresent()) {
            ConcreteCell concreteCell = new ConcreteCell(val.get());
            cellsMap.put(ioVariables.get(k).getName(), concreteCell);
          } else {
            throw new ImportException("Could not parse concrete value " + cell);
          }
        }
        if (cellsMap.size() != ioVariables.size()) {
          throw new ImportException("Row too short: Do not have a cell for each IOVariable");
        }
        concreteSpec.getRows().add(new SpecificationRow<>(cellsMap));
      }
      currentCycle += currentDuration;
    }
    return concreteSpec;
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    File xsdFile = new File
        (this.getClass().getResource("/fileFormats/specification.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }
}

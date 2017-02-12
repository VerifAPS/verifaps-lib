package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.Value;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.ConcreteDuration;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import java.io.File;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author Benjamin Alt
 */
public class XmlConcreteSpecImporter extends XmlImporter<ConcreteSpecification> {

  private Unmarshaller unmarshaller;
  private List<Type> typeContext;

  public XmlConcreteSpecImporter(List<Type> typeContext) throws ImportException {
    this.typeContext = typeContext;
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

      List<ValidIoVariable> validIoVariables = importIoVariables(importedSpec
              .getVariables());
      return importConcreteSpec(validIoVariables, importedSpec);
    } catch (JAXBException  e) {
      throw new ImportException(e);
    }
  }

  private List<ValidIoVariable> importIoVariables(Variables variables)
      throws ImportException {
    List<ValidIoVariable> ioVariables = new ArrayList<>();
    for (Variables.IoVariable variable : variables.getIoVariable()) {
      try {
        VariableCategory category = VariableCategory.valueOf(variable.getIo().toUpperCase());
        Type type = typeContext.stream()
            .filter(t -> t.getTypeName().equals(variable.getDataType()))
            .findFirst()
            .orElseThrow(() -> new ImportException("Unknown variable type: " + variable.getDataType()));
        ioVariables.add(new ValidIoVariable(category, variable.getName(), type));
      } catch (IllegalArgumentException argExc) { // thrown by VariableCategory.valueOf
        throw new ImportException("Illegal variable category: " + variable.getIo());
      }
    }
    return ioVariables;
  }

  private ConcreteSpecification importConcreteSpec(List<ValidIoVariable>
      ioVariables, SpecificationTable importedSpec) throws
      ImportException {
    if (!importedSpec.isIsConcrete()) {
      throw new ImportException("Cannot import a ConcreteSpecification from a specification not " +
          "declared as concrete");
    }
    ConcreteSpecification concreteSpec = new ConcreteSpecification(importedSpec.isIsCounterExample());

    // Add the columnHeaders (column headers)
    concreteSpec.getColumnHeaders().addAll(ioVariables);

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
          Value val = ioVariables.get(k).getValidType().parseLiteral(cell)
              .orElseThrow(() -> new ImportException("Illegal value literal: " + cell));
          ConcreteCell concreteCell = new ConcreteCell(val);
          cellsMap.put(ioVariables.get(k).getName(), concreteCell);
        }
        if (cellsMap.size() != ioVariables.size()) {
          throw new ImportException("Row too short: Do not have a cell for each IOVariable");
        }
        concreteSpec.getRows().add(SpecificationRow.createUnobservableRow(cellsMap));
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

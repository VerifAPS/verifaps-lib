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

import java.io.File;
import java.net.URISyntaxException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;

import org.w3c.dom.Node;

/**
 * This class provides the functionality to import concrete specifications from xml nodes.
 *
 * @author Benjamin Alt
 */
public class XmlConcreteSpecImporter extends XmlImporter<ConcreteSpecification> {

  private Unmarshaller unmarshaller;
  private List<Type> typeContext;

  /**
   * Creates an Importer. The {@code typeContext} is later used for assigning the right type to
   * variables while importing.
   *
   * @param typeContext list of types
   * @throws ImportException Exception while marshalling
   */
  public XmlConcreteSpecImporter(List<Type> typeContext) throws ImportException {
    this.typeContext = typeContext;
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      unmarshaller = jaxbContext.createUnmarshaller();
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  /**
   * Imports a {@link ConcreteSpecification} from a xml {@link Node}.
   *
   * @param source Xml node that should be imported
   * @return Imported specification
   * @throws ImportException Exception while importing
   */
  public ConcreteSpecification doImportFromXmlNode(Node source) throws ImportException {
    try {
      SpecificationTable importedSpec =
          ((JAXBElement<SpecificationTable>) unmarshaller.unmarshal(source)).getValue();

      List<ValidIoVariable> validIoVariables = importIoVariables(importedSpec.getVariables());
      return importConcreteSpec(validIoVariables, importedSpec);
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  /**
   * Imports {@link ValidIoVariable ValidIoVariables} from {@link Variables} under use of the
   * previously specified {@code typeContext}.
   *
   * @param variables variables from which should be imported
   * @return list of valid variables
   * @throws ImportException exception while importing
   */
  private List<ValidIoVariable> importIoVariables(Variables variables) throws ImportException {
    List<ValidIoVariable> ioVariables = new ArrayList<>();
    for (Variables.IoVariable variable : variables.getIoVariable()) {
      try {
        VariableCategory category = VariableCategory.valueOf(variable.getIo().toUpperCase());
        Type type = typeContext.stream().filter(t -> t.getTypeName().equals(variable.getDataType()))
            .findFirst().orElseThrow(
                () -> new ImportException("Unknown variable type: " + variable.getDataType()));
        ioVariables.add(new ValidIoVariable(category, variable.getName(), type));
      } catch (IllegalArgumentException argExc) { // thrown by VariableCategory.valueOf
        throw new ImportException("Illegal variable category: " + variable.getIo());
      }
    }
    return ioVariables;
  }

  /**
   * Imports a {@link ConcreteSpecification} from a {@link SpecificationTable}.
   *
   * @param ioVariables defined variables
   * @param importedSpec specification table previously imported from xml
   * @return imported concrete specification
   * @throws ImportException Exception while importing
   */
  private ConcreteSpecification importConcreteSpec(List<ValidIoVariable> ioVariables,
      SpecificationTable importedSpec) throws ImportException {
    if (!importedSpec.isIsConcrete()) {
      throw new ImportException("Cannot import a ConcreteSpecification from a specification not "
          + "declared as concrete");
    }
    ConcreteSpecification concreteSpec =
        new ConcreteSpecification(importedSpec.isIsCounterExample());
    concreteSpec.setName(importedSpec.getName());

    // Add the column headers
    concreteSpec.getColumnHeaders().addAll(ioVariables);

    // Add the rows
    Rows rows = importedSpec.getRows();
    int currentCycle = 0;
    for (int i = 0; i < rows.getRow().size(); i++) {
      Rows.Row row = rows.getRow().get(i);
      int currentDuration = Integer.parseInt(row.getDuration().getValue());
      concreteSpec.getDurations().add(new ConcreteDuration(currentCycle, currentDuration));
      for (int j = 0; j < row.getCycle().size(); j++) {
        concreteSpec.getRows().add(createSpecificationRowForCycle(ioVariables, row, j));
      }
      currentCycle += currentDuration;
    }
    return concreteSpec;
  }

  /**
   * Creates a row that represents a single cycle within a {@code row}. Note that one {@code row}
   * can map to multiple {@link SpecificationRow SpecificationRows} and this method only creates the
   * row with the specified {@code cycleNum}.
   *
   * @param ioVariables IO Variables that are present in the specification
   * @param row Row which holds the information to create a specification row.
   * @param cycleNum Number of the cycle for which a row should be created
   * @return Specification row for one cycle
   * @throws ImportException Mismatch between size of {@code row} and size of {@code ioVariables}
   */
  private SpecificationRow<ConcreteCell> createSpecificationRowForCycle(
      List<ValidIoVariable> ioVariables, Rows.Row row, int cycleNum) throws ImportException {
    Map<String, ConcreteCell> cellsMap = new HashMap<>();
    Rows.Row.Cycle cycle = row.getCycle().get(cycleNum);
    if (cycle.getCell().size() != ioVariables.size()) {
      throw new ImportException("Row too short: Do not have a cell for each IOVariable");
    }
    for (int k = 0; k < ioVariables.size(); k++) {
      String cell = cycle.getCell().get(k);
      Value val = ioVariables.get(k).getValidType().parseLiteral(cell)
          .orElseThrow(() -> new ImportException("Illegal value literal: " + cell));
      ConcreteCell concreteCell = new ConcreteCell(val);
      cellsMap.put(ioVariables.get(k).getName(), concreteCell);
    }
    return SpecificationRow.createUnobservableRow(cellsMap);
  }

  @Override
  protected String getXsdFilePath() throws URISyntaxException {
    File xsdFile = new File(this.getClass().getResource("/fileFormats/specification.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }
}

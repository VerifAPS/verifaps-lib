package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;

import java.io.IOException;
import java.net.URL;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;

import org.w3c.dom.Node;
import edu.kit.iti.formal.stvs.io._1.*;


/**
 * This class provides the functionality to import constraint specifications from xml nodes.
 *
 * @author Benjamin Alt
 */
public class XmlConstraintSpecImporter extends XmlImporter<ConstraintSpecification> {

  private Unmarshaller unmarshaller;

  /**
   * Creates an Importer for {@link ConstraintSpecification ConstraintSpecifications}.
   *
   * @throws ImportException Exception while marshalling
   */
  public XmlConstraintSpecImporter() throws ImportException {
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      unmarshaller = jaxbContext.createUnmarshaller();
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  /**
   * Imports a {@link ConstraintSpecification} from a xml {@link Node}.
   *
   * @param source Xml node that should be imported
   * @return Imported specification
   * @throws ImportException Exception while importing
   */
  @Override
  public ConstraintSpecification doImportFromXmlNode(Node source) throws ImportException {
    try {
      SpecificationTable importedSpec =
          ((JAXBElement<SpecificationTable>) unmarshaller.unmarshal(source)).getValue();

      FreeVariableList freeVariables = importFreeVariableSet(importedSpec.getVariables());
      List<SpecIoVariable> ioVariables = importIoVariables(importedSpec.getVariables());
      return importConstraintSpec(freeVariables, ioVariables, importedSpec);
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  /**
   * Imports a {@link ConstraintSpecification} from a {@link SpecificationTable}.
   *
   * @param ioVariables defined variables
   * @param importedSpec specification table previously imported from xml
   * @return imported constraint specification
   * @throws ImportException Exception while importing
   */
  private ConstraintSpecification importConstraintSpec(FreeVariableList freeVariables,
      List<SpecIoVariable> ioVariables, SpecificationTable importedSpec) throws ImportException {
    ConstraintSpecification constraintSpec = new ConstraintSpecification(freeVariables);
    constraintSpec.setName(importedSpec.getName());

    // Add the columnHeaders (column headers)
    for (SpecIoVariable specIoVariable : ioVariables) {
      constraintSpec.getColumnHeaders().add(specIoVariable);
    }

    // Add the rowsj
    Rows rows = importedSpec.getRows();
    if(rows!=null) {
        for (int i = 0; i < rows.getRow().size(); i++) {
            Rows.Row row = rows.getRow().get(i);
            ConstraintDuration newDuration = new ConstraintDuration(row.getDuration().getValue());
            newDuration.setComment(row.getDuration().getComment());
            constraintSpec.getDurations().add(newDuration);
            SpecificationRow<ConstraintCell> row1 = createSpecificationRowForCycle(ioVariables, row);
            constraintSpec.getRows().add(row1);
        }
    }

    constraintSpec.setComment(importedSpec.getComment());
    return constraintSpec;
  }

  /**
   * Creates a {@link SpecificationRow} that represents a {@code row}.
   *
   * @param ioVariables IO Variables that are present in the specification
   * @param row Row which holds the information to create a specification row.
   * @return Specification row
   * @throws ImportException Mismatch between size of {@code row} and size of {@code ioVariables}
   */
  private SpecificationRow<ConstraintCell> createSpecificationRowForCycle(
      List<SpecIoVariable> ioVariables, Rows.Row row) throws ImportException {
    Map<String, ConstraintCell> cellsMap = new HashMap<>();
    for (int j = 0; j < row.getCell().size(); j++) {
      Rows.Row.Cell cell = row.getCell().get(j);
      ConstraintCell constraintCell = new ConstraintCell(cell.getValue());
      constraintCell.setComment(cell.getComment());
      cellsMap.put(ioVariables.get(j).getName(), constraintCell);
    }
    if (cellsMap.size() != ioVariables.size()) {
      throw new ImportException("Row too short: Do not have a cell for each IOVariable");
    }
    SpecificationRow<ConstraintCell> newRow = ConstraintSpecification.createRow(cellsMap);
    newRow.setComment(row.getComment());
    return newRow;
  }

  /**
   * Imports {@link SpecIoVariable SpecIoVariables} from {@link Variables}.
   *
   * @param variables variables from which should be imported
   * @return list of specification variables
   * @throws ImportException exception while importing
   */
  protected List<SpecIoVariable> importIoVariables(Variables variables) throws ImportException {
    List<SpecIoVariable> ioVariables = new ArrayList<>();
    for (Variables.IoVariable variable : variables.getIoVariable()) {
      try {
        VariableCategory category = VariableCategory.valueOf(variable.getIo().toUpperCase());
        SpecIoVariable specIoVariable =
            new SpecIoVariable(category, variable.getDataType(), variable.getName());
        if (variable.getColwidth() != null) {
          specIoVariable.getColumnConfig().setWidth(variable.getColwidth().doubleValue());
        }
        ioVariables.add(specIoVariable);
      } catch (IllegalArgumentException argExc) { // thrown by VariableCategory.valueOf
        throw new ImportException("Illegal variable category: " + variable.getIo());
      }
    }
    return ioVariables;
  }

  /**
   * Imports {@link FreeVariable FreeVariables} from {@link Variables}.
   *
   * @param variables variables from which should be imported
   * @return object representing the free variables
   * @throws ImportException exception while importing
   */
  private FreeVariableList importFreeVariableSet(Variables variables) throws ImportException {
    List<FreeVariable> freeVariableSet = new ArrayList<>();
    for (Variables.FreeVariable freeVar : variables.getFreeVariable()) {
      String typeString = freeVar.getDataType();
      freeVariableSet.add(new FreeVariable(freeVar.getName(), typeString, freeVar.getDefault()));
    }
    return new FreeVariableList(freeVariableSet);
  }

  @Override
  protected URL getXsdResource() throws IOException {
    return getClass().getResource("/fileFormats/stvs-1.0.xsd");
  }
}

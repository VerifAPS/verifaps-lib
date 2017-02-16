package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
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
public class XmlConstraintSpecImporter extends XmlImporter<ConstraintSpecification> {

  private Unmarshaller unmarshaller;

  public XmlConstraintSpecImporter() throws ImportException {
    try {
      JAXBContext jaxbContext = JAXBContext.newInstance(ObjectFactory.class);
      unmarshaller = jaxbContext.createUnmarshaller();
    } catch (JAXBException e) {
      throw new ImportException(e);
    }
  }

  @Override
  public ConstraintSpecification doImportFromXmlNode(Node source) throws ImportException {
    try {
      SpecificationTable importedSpec = ((JAXBElement<SpecificationTable>) unmarshaller
          .unmarshal(source)).getValue();

      FreeVariableList freeVariables = importFreeVariableSet(importedSpec.getVariables());
      List<SpecIoVariable> ioVariables = importIoVariables(importedSpec.getVariables());
      return importConstraintSpec(freeVariables, ioVariables, importedSpec);
    } catch (JAXBException  e) {
      throw new ImportException(e);
    }
  }

  private ConstraintSpecification importConstraintSpec(FreeVariableList freeVariables,
                                                       List<SpecIoVariable> ioVariables,
                                                       SpecificationTable importedSpec)
      throws ImportException {
    ConstraintSpecification constraintSpec = new ConstraintSpecification(freeVariables);
    constraintSpec.setName(importedSpec.getName());

    // Add the columnHeaders (column headers)
    for (SpecIoVariable specIoVariable : ioVariables) {
      constraintSpec.getColumnHeaders().add(specIoVariable);
    }

    // Add the rows
    Rows rows = importedSpec.getRows();
    for (int i = 0; i < rows.getRow().size(); i++) {
      Rows.Row row = rows.getRow().get(i);
      ConstraintDuration newDuration = new ConstraintDuration(row.getDuration().getValue());
      newDuration.setComment(row.getDuration().getComment());
      constraintSpec.getDurations().add(newDuration);
      Map<String,ConstraintCell> cellsMap = new HashMap<>();
      for (int j = 0; j < row.getCell().size(); j++) {
        Rows.Row.Cell cell = row.getCell().get(j);
        ConstraintCell constraintCell = new ConstraintCell(cell.getValue());
        constraintCell.setComment(cell.getComment());
        cellsMap.put(ioVariables.get(j).getName(), constraintCell);
      }
      if (cellsMap.size() != ioVariables.size()) {
        throw new ImportException("Row too short: Do not have a cell for each IOVariable");
      }
      constraintSpec.getRows().add(ConstraintSpecification.createRow(cellsMap));
    }

    constraintSpec.setComment(importedSpec.getComment());
    return constraintSpec;
  }

  protected List<SpecIoVariable> importIoVariables(Variables variables)
      throws ImportException {
    List<SpecIoVariable> ioVariables = new ArrayList<>();
    for (Variables.IoVariable variable : variables.getIoVariable()) {
      try {
        VariableCategory category = VariableCategory.valueOf(variable.getIo().toUpperCase());
        SpecIoVariable specIoVariable = new SpecIoVariable(category, variable.getDataType(), variable.getName());
        specIoVariable.getColumnConfig().setWidth(variable.getColwidth().doubleValue());
        ioVariables.add(specIoVariable);
      } catch (IllegalArgumentException argExc) { // thrown by VariableCategory.valueOf
        throw new ImportException("Illegal variable category: " + variable.getIo());
      }
    }
    return ioVariables;
  }

  private FreeVariableList importFreeVariableSet(Variables variables)
      throws ImportException {
    List<FreeVariable> freeVariableSet = new ArrayList<>();
    for (Variables.FreeVariable freeVar : variables.getFreeVariable()) {
      String typeString = freeVar.getDataType();
      freeVariableSet.add(new FreeVariable(freeVar.getName(), typeString, freeVar.getDefault()));
    }
    return new FreeVariableList(freeVariableSet);
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    File xsdFile = new File
        (this.getClass().getResource("/fileFormats/specification.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }
}

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

import javafx.beans.property.SimpleObjectProperty;
import javafx.collections.FXCollections;
import org.w3c.dom.Node;

/**
 * @author Benjamin Alt
 */
public class XmlConstraintSpecImporter extends XmlImporter<ConstraintSpecification> {

  private Unmarshaller unmarshaller;
  private Set<Type> typeContext;

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

      List<Type> typeContext = importTypeContext(importedSpec.getEnumTypes());
      FreeVariableSet freeVariables = importFreeVariableSet(importedSpec.getVariables(), typeContext);
      List<SpecIoVariable> ioVariables = importIoVariables(importedSpec.getVariables(), typeContext);
      return importConstraintSpec(typeContext, freeVariables, ioVariables, importedSpec);
    } catch (JAXBException  e) {
      throw new ImportException(e);
    }
  }

  private ConstraintSpecification importConstraintSpec(List<Type> typeContext,
                                                       FreeVariableSet freeVariables,
                                                       List<SpecIoVariable> ioVariables,
                                                       SpecificationTable importedSpec) throws
      ImportException {
    ConstraintSpecification constraintSpec = new ConstraintSpecification(
        new SimpleObjectProperty<>(typeContext),
        new SimpleObjectProperty<>(new ArrayList<>()),
        freeVariables);

    // Add the specIoVariables (column headers)
    for (SpecIoVariable specIoVariable : ioVariables) {
      constraintSpec.getSpecIoVariables().add(specIoVariable);
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
      constraintSpec.getRows().add(new SpecificationRow<>(cellsMap));
    }

    constraintSpec.setComment(importedSpec.getComment());
    return constraintSpec;
  }

  protected List<Type> importTypeContext(EnumTypes enumTypes) throws ImportException {
    List<Type> typeContext = new ArrayList<>();
    // Type context are user-defined enums + int + bool
    typeContext.add(TypeInt.INT);
    typeContext.add(TypeBool.BOOL);
    for (EnumTypes.Enum enumT : enumTypes.getEnum()) {
      List<String> literals = enumT.getLiteral();
      typeContext.add(TypeFactory.enumOfName(enumT.getName(), literals.toArray(new
          String[literals.size()])));
    }
    return typeContext;
  }

  protected List<SpecIoVariable> importIoVariables(Variables variables, List<Type> typeContext)
      throws
      ImportException {
    List<SpecIoVariable> ioVariables = new ArrayList<>();
    for (Variables.IoVariable variable : variables.getIoVariable()) {
      Type type = typeContext.stream()
          .filter(testType -> testType.getTypeName().equals(variable.getDataType()))
          .findAny()
          .orElseThrow(() ->
              new ImportException(
                  "Type " + variable.getDataType() + " not found for free "
                  + "variable " + variable.getName()));

      try {
        VariableCategory category = VariableCategory.valueOf(variable.getIo().toUpperCase());
        ioVariables.add(new SpecIoVariable(category, type, variable.getName()));
      } catch (IllegalArgumentException argExc) {
        throw new ImportException("Illegal variable category: " + variable.getIo());
      }
    }
    return ioVariables;
  }

  private FreeVariableSet importFreeVariableSet(Variables variables, List<Type> typeContext)
      throws ImportException {
    try {
      List<FreeVariable> freeVariableSet = new ArrayList<>();
      for (Variables.FreeVariable freeVar : variables.getFreeVariable()) {
        boolean typeFound = false;
        String typeString = freeVar.getDataType();
        for (Type type : typeContext) {
          if (type.getTypeName().equals(typeString)) {
            typeFound = true;
            FreeVariable freeVariable = new FreeVariable(freeVar.getName(), type);
            if (freeVar.getDefault() != null) {
              Optional<Value> val = type.parseLiteral(freeVar.getDefault());
              if (val.isPresent()) {
                freeVariable.setDefaultValue(val.get());
              }
            }
            freeVariableSet.add(freeVariable);
          }
        }
        if (!typeFound) {
          throw new ImportException("Type " + freeVar.getDataType() + " not found for free " +
              "variable " + freeVar.getName());
        }
      }
      return new FreeVariableSet(freeVariableSet);
    } catch (IllegalValueTypeException e) {
      throw new ImportException(e);
    }
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    File xsdFile = new File
        (this.getClass().getResource("/fileFormats/specification.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }
}

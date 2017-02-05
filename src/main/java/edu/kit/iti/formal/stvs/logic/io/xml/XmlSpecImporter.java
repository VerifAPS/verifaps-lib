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
public class XmlSpecImporter extends XmlImporter<ConstraintSpecification> {

  private Unmarshaller unmarshaller;
  private Set<Type> typeContext;

  public XmlSpecImporter() throws ImportException {
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

      Set<Type> typeContext = importTypeContext(importedSpec.getEnumTypes());
      FreeVariableSet freeVariables = importFreeVariableSet(importedSpec.getVariables(), typeContext);
      List<SpecIoVariable> ioVariables = importIoVariables(importedSpec.getVariables(), typeContext);
      return importConstraintSpec(typeContext, freeVariables, ioVariables, importedSpec);
    } catch (JAXBException  e) {
      throw new ImportException(e);
    }
  }

  public ConcreteSpecification doImportConcreteFromXmlNode(Node source) throws ImportException {
    try {
      SpecificationTable importedSpec = ((JAXBElement<SpecificationTable>) unmarshaller
          .unmarshal(source)).getValue();

      Set<Type> typeContext = importTypeContext(importedSpec.getEnumTypes());
      List<SpecIoVariable> ioVariables = importIoVariables(importedSpec.getVariables(), typeContext);
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

    // Add a column for each ioVariable
    Variables variables = importedSpec.getVariables();
    for (int i = 0; i < variables.getIoVariable().size(); i++) {
      Variables.IoVariable ioVar = variables.getIoVariable().get(i);
      int colWidth = ioVar.getColwidth().intValue();
      SpecIoVariable specIoVariable = ioVariables.get(i);
      specIoVariable.getColumnConfig().setWidth(colWidth);
      concreteSpec.getSpecIoVariables().add(specIoVariable);
    }

    // Add the rows
    Rows rows = importedSpec.getRows();
    int currentCycle = 0;
    for (int i = 0; i < rows.getRow().size(); i++) {
      Rows.Row row = rows.getRow().get(i);
      int currentDuration = Integer.parseInt(row.getDuration().getValue());
      concreteSpec.getDurations().add(new ConcreteDuration(currentCycle, currentDuration));
      Map<String,ConcreteCell> cellsMap = new HashMap<>();
      for (int j = 0; j < row.getCell().size(); j++){
        Rows.Row.Cell cell = row.getCell().get(j);
        Type cellType = ioVariables.get(i).getType();
        Optional<Value> val = cellType.parseLiteral(cell.getValue());
        if (val.isPresent()) {
          ConcreteCell concreteCell = new ConcreteCell(val.get());
          cellsMap.put(ioVariables.get(i).getName(), concreteCell);
        } else {
          throw new ImportException("Could not parse concrete value " + cell.getValue());
        }
      }
      if (cellsMap.size() != ioVariables.size()) {
        throw new ImportException("Row too short: Do not have a cell for each IOVariable");
      }
      concreteSpec.getRows().add(new SpecificationRow<>(cellsMap));
      currentCycle += currentDuration;
    }
    return concreteSpec;
  }

  private ConstraintSpecification importConstraintSpec(Set<Type> typeContext,
                                                       FreeVariableSet freeVariables,
                                                       List<SpecIoVariable> ioVariables,
                                                       SpecificationTable importedSpec) throws
      ImportException {
    ConstraintSpecification constraintSpec = new ConstraintSpecification(
        FXCollections.observableSet(typeContext), FXCollections.observableSet(), freeVariables);

    // Add a column for each ioVariable
    Variables variables = importedSpec.getVariables();
    for (int i = 0; i < variables.getIoVariable().size(); i++) {
      Variables.IoVariable ioVar = variables.getIoVariable().get(i);
      int colWidth = ioVar.getColwidth().intValue();
      SpecIoVariable specIoVariable = ioVariables.get(i);
      specIoVariable.getColumnConfig().setWidth(colWidth);
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
      for (Rows.Row.Cell cell : row.getCell()) {
        ConstraintCell constraintCell = new ConstraintCell(cell.getValue());
        constraintCell.setComment(cell.getComment());
        cellsMap.put(ioVariables.get(i).getName(), constraintCell);
      }
      if (cellsMap.size() != ioVariables.size()) {
        throw new ImportException("Row too short: Do not have a cell for each IOVariable");
      }
      constraintSpec.getRows().add(new SpecificationRow<>(cellsMap));
    }

    constraintSpec.setComment(importedSpec.getComment());
    return constraintSpec;
  }

  private Set<Type> importTypeContext(EnumTypes enumTypes) throws ImportException {
    Set<Type> typeContext = new HashSet<>();
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

  private List<SpecIoVariable> importIoVariables(Variables variables, Set<Type> typeContext)
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

  private FreeVariableSet importFreeVariableSet(Variables variables, Set<Type> typeContext) throws ImportException {
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
          if (!typeFound) {
            throw new ImportException("Type " + freeVar.getDataType() + " not found for free " +
                "variable " + freeVar.getName());
          }
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

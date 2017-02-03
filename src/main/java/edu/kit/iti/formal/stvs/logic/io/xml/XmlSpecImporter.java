package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.exteta_1.ConstraintVariable;
import edu.kit.iti.formal.exteta_1.Step;
import edu.kit.iti.formal.exteta_1.TestTable;
import edu.kit.iti.formal.exteta_1.Variable;
import edu.kit.iti.formal.exteta_1.VariableIdentifier;
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
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import org.w3c.dom.Node;

import static com.sun.org.apache.xalan.internal.xsltc.compiler.sym.Literal;

/**
 * @author Benjamin Alt
 */
public class XmlSpecImporter extends XmlImporter<ConstraintSpecification> {

  private Unmarshaller unmarshaller;

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

      TestTable testTable = importedSpec.getTestTable();
      AdditionalInfo additionalInfo = importedSpec.getAdditionalInfo();
      DisplayInfo displayInfo = importedSpec.getDisplayInfo();

      Set<Type> typeContext = importTypeContext(additionalInfo);
      FreeVariableSet freeVariables = importFreeVariableSet(testTable, additionalInfo);
      List<SpecIoVariable> ioVariables = importIoVariables(testTable, additionalInfo);
      return importConstraintSpec(typeContext, freeVariables,
          ioVariables, testTable, additionalInfo, displayInfo);
    } catch (JAXBException  e) {
      throw new ImportException(e);
    }
  }

  public ConcreteSpecification doImportConcreteFromXmlNode(Node source) throws ImportException {
    try {
      SpecificationTable importedSpec = ((JAXBElement<SpecificationTable>) unmarshaller
          .unmarshal(source)).getValue();

      TestTable testTable = importedSpec.getTestTable();
      AdditionalInfo additionalInfo = importedSpec.getAdditionalInfo();
      DisplayInfo displayInfo = importedSpec.getDisplayInfo();

      return importConcreteSpec(importedSpec, testTable, additionalInfo,
          displayInfo);

    } catch (JAXBException  e) {
      throw new ImportException(e);
    }
  }

  private ConcreteSpecification importConcreteSpec(SpecificationTable importedSpec, TestTable testTable, AdditionalInfo additionalInfo, DisplayInfo displayInfo) throws ImportException {
    if (!importedSpec.isIsConcrete()) {
      throw new ImportException("Cannot import a ConcreteSpecification from a specification not " +
          "declared as concrete");
    }
    ConcreteSpecification concreteSpec = new ConcreteSpecification(importedSpec.isIsCounterExample());
    for (SpecIoVariable ioVar : importIoVariables(testTable, additionalInfo)) {
      concreteSpec.getColumns().add(new SpecificationColumn<>(ioVar, new ArrayList<>(), new
          ColumnConfig()));
    }

    List<Object> steps = testTable.getSteps().getBlockOrStep();
    for (int i = 0; i < steps.size(); i++) {
      if (steps.get(i) instanceof Step) {
        Step step = (Step) steps.get(i);
        concreteSpec.getDurations().add(new ConstraintDuration(step.getDuration()));
        Map<String, ConstraintCell> rowCells = new HashMap<>();
        List<String> cellEntries = step.getCell();
        for (int j = 0; j < cellEntries.size(); j++) {
          SpecIoVariable variable = ioVariables.get(j);
          rowCells.put(variable.getName(), new ConstraintCell(cellEntries.get(i)));
        }
        constraintSpec.getRows().add(i, new SpecificationRow<>(rowCells));
      }
    }

    // Display info
    for (DisplayInfo.IoVariables.VariableIdentifier variableId : displayInfo.getIoVariables()
        .getVariableIdentifier()) {
      for (SpecificationColumn<ConstraintCell> col : constraintSpec.getColumns()) {
        if (col.getSpecIoVariable().getName().equals(variableId.getName())) {
          col.getConfig().setWidth(variableId.getColWidth().intValue());
        }
      }
    }

    // Additional info
    for (AdditionalInfo.IoVariables.VariableIdentifier variableId : additionalInfo.getIoVariables
        ().getVariableIdentifier()) {
      for (SpecificationColumn<ConstraintCell> col : constraintSpec.getColumns()) {
        if (col.getSpecIoVariable().getName().equals(variableId.getName())) {
          col.setComment(variableId.getComment());
        }
      }
    }
    for (AdditionalInfo.Rows.Row row : additionalInfo.getRows().getRow()) {
      SpecificationRow<ConstraintCell> concernedRow = constraintSpec.getRows().get(Integer.parseInt
          (row.getId()));
      concernedRow.setComment(row.getComment());
      for (AdditionalInfo.Rows.Row.VariableIdentifier variableId : row.getVariableIdentifier()) {
        concernedRow.getCells().get(variableId.getName()).setComment(variableId.getComment());
      }
    }
    constraintSpec.setComment(additionalInfo.getTable().getComment());

    return constraintSpec;
  }

  private ConstraintSpecification importConstraintSpec(Set<Type> typeContext,
                                                       FreeVariableSet freeVariables,
                                                       List<SpecIoVariable> ioVariables,
                                                       TestTable testTable,
                                                       AdditionalInfo additionalInfo,
                                                       DisplayInfo displayInfo) {
    ConstraintSpecification constraintSpec = new ConstraintSpecification
        (typeContext, new HashSet<>(), freeVariables);
    for (SpecIoVariable ioVar : ioVariables) {
      constraintSpec.getColumns().add(new SpecificationColumn<>(ioVar, new ArrayList<>(), new
          ColumnConfig()));
    }

    List<Object> steps = testTable.getSteps().getBlockOrStep();
    for (int i = 0; i < steps.size(); i++) {
      if (steps.get(i) instanceof Step) {
        Step step = (Step) steps.get(i);
        constraintSpec.getDurations().add(new ConstraintDuration(step.getDuration()));
        Map<String, ConstraintCell> rowCells = new HashMap<>();
        List<String> cellEntries = step.getCell();
        for (int j = 0; j < cellEntries.size(); j++) {
          SpecIoVariable variable = ioVariables.get(j);
          rowCells.put(variable.getName(), new ConstraintCell(cellEntries.get(i)));
        }
        constraintSpec.getRows().add(i, new SpecificationRow<>(rowCells));
      }
    }

    // Display info
    for (DisplayInfo.IoVariables.VariableIdentifier variableId : displayInfo.getIoVariables()
        .getVariableIdentifier()) {
      for (SpecificationColumn<ConstraintCell> col : constraintSpec.getColumns()) {
        if (col.getSpecIoVariable().getName().equals(variableId.getName())) {
          col.getConfig().setWidth(variableId.getColWidth().intValue());
        }
      }
    }

    // Additional info
    for (AdditionalInfo.IoVariables.VariableIdentifier variableId : additionalInfo.getIoVariables
        ().getVariableIdentifier()) {
      for (SpecificationColumn<ConstraintCell> col : constraintSpec.getColumns()) {
        if (col.getSpecIoVariable().getName().equals(variableId.getName())) {
          col.setComment(variableId.getComment());
        }
      }
    }
    for (AdditionalInfo.Rows.Row row : additionalInfo.getRows().getRow()) {
      SpecificationRow<ConstraintCell> concernedRow = constraintSpec.getRows().get(Integer.parseInt
          (row.getId()));
      concernedRow.setComment(row.getComment());
      for (AdditionalInfo.Rows.Row.VariableIdentifier variableId : row.getVariableIdentifier()) {
        concernedRow.getCells().get(variableId.getName()).setComment(variableId.getComment());
      }
    }
    constraintSpec.setComment(additionalInfo.getTable().getComment());

    return constraintSpec;
  }

  private Set<Type> importTypeContext(AdditionalInfo additionalInfo) throws ImportException {
    Set<Type> typeContext = new HashSet<>();
    // Type context are user-defined enums + int + bool
    typeContext.add(TypeInt.INT);
    typeContext.add(TypeBool.BOOL);
    for (AdditionalInfo.IoVariables.VariableIdentifier variableId : additionalInfo.getIoVariables
        ().getVariableIdentifier()) {
      Type enumType = getEnumType(additionalInfo, variableId.getName());
        typeContext.add(enumType);
    }
    return typeContext;
  }

  private List<SpecIoVariable> importIoVariables(TestTable testTable, AdditionalInfo additionalInfo) throws
      ImportException {
    List<SpecIoVariable> ioVariables = new ArrayList<>();
    List<Variable> variables = testTable.getVariables().getVariableOrConstraint();
    for (Variable variable : variables) {
      if (variable instanceof VariableIdentifier) {
        Type type = getVariableType(additionalInfo, variable);
        String name = variable.getName();
        String category = ((VariableIdentifier) variable).getIo();
        if (category.equals("input")) {
          ioVariables.add(new SpecIoVariable(VariableCategory.INPUT, type, name));
        } else if (category.equals("output")) {
          ioVariables.add(new SpecIoVariable(VariableCategory.OUTPUT, type, name));
        } else {
          throw new ImportException("Illegal variable category: " + category);
        }
      }
    }
    return ioVariables;
  }

  private Type getVariableType(AdditionalInfo additionalInfo, Variable variable) throws ImportException {
    Type type = getVariableType(additionalInfo, variable);
    String typeString = variable.getDataType().value();
    if (typeString.equals("INT")) {
      return TypeInt.INT;
    } else if (typeString.equals("BOOLEAN")) {
      return TypeBool.BOOL;
    } else if (typeString.equals("ENUM")) {
      return getEnumType(additionalInfo, variable.getName());
    } else {
      throw new ImportException("Unsupported type: " + typeString);
    }
  }

  private Type getEnumType(AdditionalInfo additionalInfo, String variableName) throws ImportException {
    for (AdditionalInfo.IoVariables.VariableIdentifier variableId : additionalInfo.getIoVariables
        ().getVariableIdentifier()) {
      if (variableId.getName().equals(variableName)) {
        String enumName = variableId.getEnumType();
        if (enumName != null) {
          List<String> literals = new ArrayList<>();
          boolean found = false;
          for (AdditionalInfo.Enums.Enum enumT : additionalInfo.getEnums().getEnum()) {
            if (enumT.getName().equals(enumName)) {
              found = true;
              literals = enumT.getLiteral();
            }
          }
          if (!found) {
            throw new ImportException("Enum type " + enumName + "not declared in " +
                "'enums' section of AdditionalInfo");
          }
          return TypeFactory.enumOfName(enumName, literals.toArray(new String[literals
              .size()]));
        }
      }
    }
    throw new ImportException("Enum type not declared for variable " + variableName);
  }

  private FreeVariableSet importFreeVariableSet(TestTable testTable, AdditionalInfo
      additionalInfo) throws ImportException {
    try {
      List<FreeVariable> freeVariables = new ArrayList<>();
      List<AdditionalInfo.ConstraintVariables.ConstraintVariable>
          additionalInfoConstraintVars = additionalInfo
          .getConstraintVariables().getConstraintVariable();
      List<Variable> variables = testTable.getVariables().getVariableOrConstraint();
      for (Variable variable : variables) {
        if (variable instanceof ConstraintVariable) {
          String constraintVarName = variable.getName();
          String constraintVarTypeString = variable.getDataType().value();
          Type constraintVarType = getVariableType(additionalInfo, variable);
          FreeVariable freeVar = new FreeVariable(constraintVarName, constraintVarType);
          // Find out the default value
          for (AdditionalInfo.ConstraintVariables.ConstraintVariable cv :
              additionalInfoConstraintVars) {
            if (cv.getName().equals(constraintVarName)) {
              if (constraintVarType.equals(TypeInt.INT)) {
                freeVar.setDefaultValue(new ValueInt(Integer.parseInt(cv.getDefaultValue())));
              } else if (constraintVarType.equals(TypeBool.BOOL)) {
                ValueBool valueBool = Boolean.parseBoolean(cv.getDefaultValue()) ? ValueBool.TRUE
                    : ValueBool.FALSE;
                freeVar.setDefaultValue(valueBool);
              }
            }
          }
          freeVariables.add(freeVar);
        }
      }
      return new FreeVariableSet(freeVariables);
    } catch (IllegalValueTypeException e) {
      throw new ImportException(e);
    }
  }

  @Override
  protected String getXSDFilePath() throws URISyntaxException {
    File xsdFile = new File
        (this.getClass().getResource("/fileFormats/config.xsd").toURI());
    return xsdFile.getAbsolutePath();
  }
}

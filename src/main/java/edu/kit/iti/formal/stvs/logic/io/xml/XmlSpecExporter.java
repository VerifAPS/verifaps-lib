package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.ValueEnum;
import edu.kit.iti.formal.stvs.model.table.*;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBElement;
import java.math.BigInteger;
import java.util.ArrayList;
import java.util.List;

/**
 * @author Benjamin Alt
 */
public class XmlSpecExporter extends XmlExporter<ConstraintSpecification> {

  private ObjectFactory objectFactory;

  public XmlSpecExporter() {
    objectFactory = new ObjectFactory();
  }

  @Override
  public Node exportToXmlNode(ConstraintSpecification source) throws ExportException {
    edu.kit.iti.formal.stvs.logic.io.xml.SpecificationTable specTable = objectFactory.createSpecificationTable();
    specTable.setVariables(makeVariables(source));
    specTable.setRows(makeRows(source));
    specTable.setEnumTypes(makeEnumTypes(source));
    specTable.setComment(source.getComment());
    specTable.setIsConcrete(false);
    JAXBElement<edu.kit.iti.formal.stvs.logic.io.xml.SpecificationTable> element = objectFactory.createSpecification(specTable);
    return marshalToNode(element);
  }

  public Node exportToXmlNode(ConcreteSpecification source) throws ExportException {
    edu.kit.iti.formal.stvs.logic.io.xml.SpecificationTable specTable = objectFactory.createSpecificationTable();
    specTable.setVariables(makeVariables(source));
    specTable.setEnumTypes(makeEnumTypes(source));
    specTable.setRows(makeRows(source));
    specTable.setIsConcrete(true);
    JAXBElement<edu.kit.iti.formal.stvs.logic.io.xml.SpecificationTable> element = objectFactory.createSpecification(specTable);
    return marshalToNode(element);
  }


  private Rows makeRows(ConcreteSpecification concreteSpec) {
    Rows rows = objectFactory.createRows();
    int currentCycle = 0;
    for (int i = 0; i < concreteSpec.getDurations().size(); i++) {;
      Rows.Row exportRow = objectFactory.createRowsRow();
      Rows.Row.Duration duration = objectFactory.createRowsRowDuration();
      int currentDuration = concreteSpec.getDurations().get(i).getDuration();
      duration.setValue(Integer.toString(currentDuration));
      exportRow.setDuration(duration);
      for (int j = currentCycle; j < currentCycle + currentDuration; j++) {
        // This now corresponds to a cycle
        Rows.Row.Cycle cycle = objectFactory.createRowsRowCycle();
        for (SpecificationColumn<ConcreteCell> col : concreteSpec.getColumns()) {
          ConcreteCell cell = col.getCells().get(i);
          cycle.getCell().add(cell.getValue().getValueString());
        }
        exportRow.getCycle().add(cycle);
      }
      rows.getRow().add(exportRow);
      currentCycle += concreteSpec.getDurations().get(i).getDuration();
    }
    return rows;
  }

  private Rows makeRows(ConstraintSpecification constraintSpec) {
    Rows rows = objectFactory.createRows();
    for (int i = 0; i < constraintSpec.getRows().size(); i++) {
      SpecificationRow<ConstraintCell> row = constraintSpec.getRows().get(i);
      Rows.Row exportRow = objectFactory.createRowsRow();
      exportRow.setComment(row.getComment());
      Rows.Row.Duration duration = objectFactory.createRowsRowDuration();
      duration.setValue(constraintSpec.getDurations().get(i).getAsString());
      duration.setComment(constraintSpec.getDurations().get(i).getComment());
      exportRow.setDuration(duration);
      for (ConstraintCell cell : row.getCells().values()) {
        Rows.Row.Cell exportCell = objectFactory.createRowsRowCell();
        exportCell.setComment(cell.getComment());
        exportCell.setValue(cell.getAsString());
        exportRow.getCell().add(exportCell);
      }
      rows.getRow().add(exportRow);
    }
    return rows;
  }

  private EnumTypes makeEnumTypes(SpecificationTable<?,?> specTable) {
    EnumTypes enumTypes = objectFactory.createEnumTypes();
    for (int i = 0; i < specTable.getColumns().size(); i++) {
      SpecificationColumn<?> col = specTable.getColumns().get(i);
      Type type = col.getSpecIoVariable().getType();
      if (type instanceof TypeEnum) {
        EnumTypes.Enum exportEnumType = objectFactory.createEnumTypesEnum();
        exportEnumType.setName(type.getTypeName());
        for (ValueEnum literal : ((TypeEnum) type).getValues()) {
         exportEnumType.getLiteral().add(literal.getValueString());
       }
       enumTypes.getEnum().add(exportEnumType);
      }
    }
    return enumTypes;
  }

  private Variables makeVariables(ConstraintSpecification constraintSpec) {
    Variables variables = objectFactory.createVariables();
    variables.getIoVariable().addAll(makeIoVariables(constraintSpec));

    for (FreeVariable freeVariable : constraintSpec.getFreeVariableSet().getVariableSet()) {
      Variables.FreeVariable freeVar = objectFactory.createVariablesFreeVariable();
      freeVar.setName(freeVariable.getName());
      freeVar.setDataType(freeVariable.getType().getTypeName());
      freeVar.setDefault(freeVariable.getDefaultValue().getValueString());
      variables.getFreeVariable().add(freeVar);
    }
    return variables;
  }

  private Variables makeVariables(ConcreteSpecification concreteSpec) {
    Variables variables = objectFactory.createVariables();
    variables.getIoVariable().addAll(makeIoVariables(concreteSpec));
    return variables;
  }

  private List<Variables.IoVariable> makeIoVariables(SpecificationTable<?,?> specTable) {
    List<Variables.IoVariable> variables = new ArrayList<>();
    for (SpecificationColumn col : specTable.getColumns()) {
      Variables.IoVariable ioVar = objectFactory.createVariablesIoVariable();
      //ioVar.setComment(col.getComment()); //TODO column not commentable yet
      ioVar.setColwidth(BigInteger.valueOf(col.getConfig().getWidth()));
      ioVar.setDataType(col.getSpecIoVariable().getType().getTypeName());
      if (col.getSpecIoVariable().getCategory() == VariableCategory.INPUT) {
        ioVar.setIo("input");
      } else {
        ioVar.setIo("output");
      }
      ioVar.setName(col.getSpecIoVariable().getName());
      variables.add(ioVar);
    }
    return variables;
  }
}

package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
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
public class XmlConstraintSpecExporter extends XmlExporter<ConstraintSpecification> {

  private ObjectFactory objectFactory;

  public XmlConstraintSpecExporter() {
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
      for (SpecIoVariable ioVariable : constraintSpec.getSpecIoVariables()) {
        ConstraintCell cell = row.getCells().get(ioVariable.getName());
        Rows.Row.Cell exportCell = objectFactory.createRowsRowCell();
        exportCell.setComment(cell.getComment());
        exportCell.setValue(cell.getAsString());
        exportRow.getCell().add(exportCell);
      }
      rows.getRow().add(exportRow);
    }
    return rows;
  }

  protected EnumTypes makeEnumTypes(SpecificationTable<?, ?> specTable) {
    EnumTypes enumTypes = objectFactory.createEnumTypes();
    for (SpecIoVariable ioVar : specTable.getSpecIoVariables()) {
      Type type = ioVar.getType();
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
      if (freeVariable.getDefaultValue() != null) {
        freeVar.setDefault(freeVariable.getDefaultValue().getValueString());
      }
      variables.getFreeVariable().add(freeVar);
    }
    return variables;
  }

  private Variables makeVariables(ConcreteSpecification concreteSpec) {
    Variables variables = objectFactory.createVariables();
    variables.getIoVariable().addAll(makeIoVariables(concreteSpec));
    return variables;
  }

  protected List<Variables.IoVariable> makeIoVariables(SpecificationTable<?, ?> specTable) {
    List<Variables.IoVariable> variables = new ArrayList<>();
    for (SpecIoVariable specIoVariable : specTable.getSpecIoVariables()) {
      Variables.IoVariable ioVar = objectFactory.createVariablesIoVariable();
      ioVar.setComment(ioVar.getComment());
      ioVar.setColwidth(BigInteger.valueOf(specIoVariable.getColumnConfig().getWidth()));
      ioVar.setDataType(specIoVariable.getType().getTypeName());
      ioVar.setIo(specIoVariable.getCategory().toString().toLowerCase());
      ioVar.setName(specIoVariable.getName());
      variables.add(ioVar);
    }
    return variables;
  }
}

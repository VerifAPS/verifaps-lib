package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.IoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.table.*;
import edu.kit.iti.formal.stvs.model.table.SpecificationTable;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBElement;
import java.math.BigInteger;
import java.util.stream.Collectors;

/**
 * @author Benjamin Alt
 */
public class XmlConstraintSpecExporter extends XmlExporter<ConstraintSpecification> {

  private static ObjectFactory objectFactory;

  public XmlConstraintSpecExporter() {
    objectFactory = new ObjectFactory();
  }

  @Override
  public Node exportToXmlNode(ConstraintSpecification source) throws ExportException {
    edu.kit.iti.formal.stvs.logic.io.xml.SpecificationTable specTable = objectFactory.createSpecificationTable();
    specTable.setVariables(makeVariables(source));
    specTable.setRows(makeRows(source));
    specTable.setComment(source.getComment());
    specTable.setIsConcrete(false);
    specTable.setName(source.getName());
    JAXBElement<edu.kit.iti.formal.stvs.logic.io.xml.SpecificationTable> element = objectFactory.createSpecification(specTable);
    return marshalToNode(element, "edu.kit.iti.formal.stvs.logic.io.xml");
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
      for (SpecIoVariable ioVariable : constraintSpec.getColumnHeaders()) {
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

  private Variables makeVariables(ConstraintSpecification constraintSpec) {
    Variables variables = objectFactory.createVariables();
    variables.getIoVariable().addAll(constraintSpec.getColumnHeaders().stream()
      .map(this::makeIoVariablesFromSpec).collect(Collectors.toList()));

    for (FreeVariable freeVariable : constraintSpec.getFreeVariableList().getVariables()) {
      Variables.FreeVariable freeVar = objectFactory.createVariablesFreeVariable();
      freeVar.setName(freeVariable.getName());
      freeVar.setDataType(freeVariable.getType());
      if (freeVariable.getDefaultValue() != "") {
        freeVar.setDefault(freeVariable.getDefaultValue());
      }
      variables.getFreeVariable().add(freeVar);
    }
    return variables;
  }

  protected static  Variables.IoVariable makeIoVariable(IoVariable validIoVariable) {
    Variables.IoVariable ioVar = objectFactory.createVariablesIoVariable();
    ioVar.setComment(ioVar.getComment());
    ioVar.setDataType(validIoVariable.getType());
    ioVar.setIo(validIoVariable.getCategory().toString().toLowerCase());
    ioVar.setName(validIoVariable.getName());
    return ioVar;
  }

  protected Variables.IoVariable makeIoVariablesFromSpec(SpecIoVariable specIoVariable) {
    Variables.IoVariable ioVar = makeIoVariable(specIoVariable);
    ioVar.setColwidth(BigInteger.valueOf((long) specIoVariable.getColumnConfig().getWidth()));
    return ioVar;
  }
}

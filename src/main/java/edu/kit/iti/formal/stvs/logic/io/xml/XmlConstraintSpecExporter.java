package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.FreeVariable;
import edu.kit.iti.formal.stvs.model.common.IoVariable;
import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;

import java.math.BigInteger;
import java.util.stream.Collectors;
import javax.xml.bind.JAXBElement;

import org.w3c.dom.Node;

/**
 * This class provides the functionality to export {@link ConstraintSpecification
 * ConstraintSpecifications} to xml nodes.
 *
 * @author Benjamin Alt
 */
public class XmlConstraintSpecExporter extends XmlExporter<ConstraintSpecification> {

  private ObjectFactory objectFactory;

  public XmlConstraintSpecExporter() {
    objectFactory = new ObjectFactory();
  }

  /**
   * Exports a given {@link ConstraintSpecification} as a XML {@link Node}.
   *
   * @param source The specification that should be exported
   * @return The XML Node representing the specification
   * @throws ExportException Exception during marshalling
   */
  @Override
  public Node exportToXmlNode(ConstraintSpecification source) throws ExportException {
    edu.kit.iti.formal.stvs.logic.io.xml.SpecificationTable specTable =
        objectFactory.createSpecificationTable();
    specTable.setVariables(makeVariables(source));
    specTable.setRows(makeRows(source));
    specTable.setComment(source.getComment());
    specTable.setIsConcrete(false);
    specTable.setName(source.getName());
    JAXBElement<edu.kit.iti.formal.stvs.logic.io.xml.SpecificationTable> element =
        objectFactory.createSpecification(specTable);
    return marshalToNode(element, NAMESPACE);
  }

  /**
   * Build {@link Rows} from a {@link ConcreteSpecification}.
   *
   * @param constraintSpec specification from which rows should be generated
   * @return rows that represent the rows of the specification
   */
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

  /**
   * Generate/Extract {@link Variables} from a {@link ConstraintSpecification}.
   *
   * @param constraintSpec specification from which variables should be generated
   * @return variables that could be generated from the specification
   */
  private Variables makeVariables(ConstraintSpecification constraintSpec) {
    Variables variables = objectFactory.createVariables();
    variables.getIoVariable().addAll(constraintSpec.getColumnHeaders().stream()
        .map(this::makeIoVariablesFromSpec).collect(Collectors.toList()));

    for (FreeVariable freeVariable : constraintSpec.getFreeVariableList().getVariables()) {
      Variables.FreeVariable freeVar = objectFactory.createVariablesFreeVariable();
      freeVar.setName(freeVariable.getName());
      freeVar.setDataType(freeVariable.getType());
      if (!freeVariable.getDefaultValue().equals("")) {
        freeVar.setDefault(freeVariable.getDefaultValue());
      }
      variables.getFreeVariable().add(freeVar);
    }
    return variables;
  }

  /**
   * Create a {@link Variables.IoVariable} from a {@link IoVariable}.
   *
   * @param validIoVariable Variable from which a {@link Variables.IoVariable} should be generated
   * @return generated {@link Variables.IoVariable}
   */
  protected Variables.IoVariable makeIoVariable(IoVariable validIoVariable) {
    Variables.IoVariable ioVar = objectFactory.createVariablesIoVariable();
    ioVar.setComment(ioVar.getComment());
    ioVar.setDataType(validIoVariable.getType());
    ioVar.setIo(validIoVariable.getCategory().toString().toLowerCase());
    ioVar.setName(validIoVariable.getName());
    return ioVar;
  }

  /**
   * Generate a {@link Variables.IoVariable} from a {@link SpecIoVariable}.
   *
   * @param specIoVariable variable to be coverted
   * @return converted variable
   */
  protected Variables.IoVariable makeIoVariablesFromSpec(SpecIoVariable specIoVariable) {
    Variables.IoVariable ioVar = makeIoVariable(specIoVariable);
    ioVar.setColwidth(BigInteger.valueOf((long) specIoVariable.getColumnConfig().getWidth()));
    return ioVar;
  }
}

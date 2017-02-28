package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBElement;
import java.util.stream.Collectors;

/**
 * This class provides the functionality to export
 * {@link ConcreteSpecification ConcreteSpecifications} to xml nodes.
 *
 * @author Benjamin Alt
 */
public class XmlConcreteSpecExporter extends XmlExporter<ConcreteSpecification> {

  private ObjectFactory objectFactory;
  private XmlConstraintSpecExporter constraintSpecExporter;

  public XmlConcreteSpecExporter() {
    objectFactory = new ObjectFactory();
    //TODO: I can't get my head around why this should be here but removing it breaks the static variable in
    //XmlConstraintSpecExporter. There is something fishy here. I will investigate this later.
    constraintSpecExporter = new XmlConstraintSpecExporter();
  }

  /**
   * Exports a given {@link ConcreteSpecification} as a XML {@link Node}.
   *
   * @param source The specification that should be exported
   * @return The XML Node representing the specification
   * @throws ExportException Exception during marshalling
   */
  public Node exportToXmlNode(ConcreteSpecification source) throws ExportException {
    edu.kit.iti.formal.stvs.logic.io.xml.SpecificationTable specTable =
        objectFactory.createSpecificationTable();
    specTable.setVariables(makeVariables(source));
    specTable.setRows(makeRows(source));
    specTable.setIsConcrete(true);
    specTable.setIsCounterExample(source.isCounterExample());
    specTable.setName(source.getName());
    JAXBElement<edu.kit.iti.formal.stvs.logic.io.xml.SpecificationTable> element =
        objectFactory.createSpecification(specTable);
    return marshalToNode(element, "edu.kit.iti.formal.stvs.logic.io.xml");
  }


  /**
   * Build {@link Rows} from a {@link ConcreteSpecification}.
   *
   * @param concreteSpec specification from which rows should be generated
   * @return rows that represent the rows of the specification
   */
  private Rows makeRows(ConcreteSpecification concreteSpec) {
    Rows rows = objectFactory.createRows();
    int currentCycle = 0;
    for (int i = 0; i < concreteSpec.getDurations().size(); i++) {
      Rows.Row exportRow = objectFactory.createRowsRow();
      Rows.Row.Duration duration = objectFactory.createRowsRowDuration();
      int currentDuration = concreteSpec.getDurations().get(i).getDuration();
      duration.setValue(Integer.toString(currentDuration));
      exportRow.setDuration(duration);
      for (int j = currentCycle; j < currentCycle + currentDuration; j++) {
        // This now corresponds to a cycle
        Rows.Row.Cycle cycle = objectFactory.createRowsRowCycle();
        for (ValidIoVariable ioVar : concreteSpec.getColumnHeaders()) {
          SpecificationColumn<ConcreteCell> col = concreteSpec.getColumnByName(ioVar.getName());
          ConcreteCell cell = col.getCells().get(j);
          cycle.getCell().add(cell.getValue().getValueString());
        }
        exportRow.getCycle().add(cycle);
      }
      rows.getRow().add(exportRow);
      currentCycle += concreteSpec.getDurations().get(i).getDuration();
    }
    return rows;
  }


  /**
   * Generate/Extract {@link Variables} from a {@link ConcreteSpecification}.
   *
   * @param concreteSpec specification from which variables should be generated
   * @return variables that could be generated from the specification
   */
  protected Variables makeVariables(ConcreteSpecification concreteSpec) {
    Variables variables = objectFactory.createVariables();
    variables.getIoVariable().addAll(concreteSpec.getColumnHeaders().stream()
        .map(XmlConstraintSpecExporter::makeIoVariable).collect(Collectors.toList()));
    return variables;
  }
}

package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
import edu.kit.iti.formal.stvs.model.table.ConcreteCell;
import edu.kit.iti.formal.stvs.model.table.ConcreteSpecification;
import edu.kit.iti.formal.stvs.model.table.SpecificationColumn;
import org.w3c.dom.Node;

import javax.xml.bind.JAXBElement;

/**
 * @author Benjamin Alt
 */
public class XmlConcreteSpecExporter extends XmlExporter<ConcreteSpecification> {

  private ObjectFactory objectFactory;
  private XmlConstraintSpecExporter constraintSpecExporter;

  public XmlConcreteSpecExporter() {
    objectFactory = new ObjectFactory();
    constraintSpecExporter = new XmlConstraintSpecExporter();
  }

  public Node exportToXmlNode(ConcreteSpecification source) throws ExportException {
    edu.kit.iti.formal.stvs.logic.io.xml.SpecificationTable specTable = objectFactory.createSpecificationTable();
    specTable.setVariables(constraintSpecExporter.makeVariables(source));
    specTable.setEnumTypes(constraintSpecExporter.makeEnumTypes(source));
    specTable.setRows(makeRows(source));
    specTable.setIsConcrete(true);
    specTable.setName(source.getName());
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

}

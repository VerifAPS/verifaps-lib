package edu.kit.iti.formal.stvs.model.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.config.ColumnConfig;

import java.util.Optional;

/**
 * @author Benjamin Alt
 */
public class SpecificationColumn<C> {

  public C getEntryForRow(int row) {
    return null;
  }

  public SpecIoVariable getSpecIoVariable() {
    return null;
  }

  public Optional<ColumnConfig> getConfig() {
    return null;
  }
}

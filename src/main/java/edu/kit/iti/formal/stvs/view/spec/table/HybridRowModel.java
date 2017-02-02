package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.table.ConstraintCell;
import edu.kit.iti.formal.stvs.model.table.ConstraintDuration;
import edu.kit.iti.formal.stvs.model.table.SpecificationRow;

import java.util.HashMap;

/**
 * Created by Philipp on 01.02.2017.
 */
public class HybridRowModel extends SpecificationRow<HybridCellModel> {

  private final HybridCellModel duration;

  public HybridRowModel(String duration) {
    this(new ConstraintDuration(duration));
  }

  public HybridRowModel(ConstraintDuration duration) {
    super(new HashMap<>());
    this.duration = new HybridCellModel(duration);
  }

  public HybridRowModel add(String column, String cell) {
    return add(column, new ConstraintCell(cell));
  }

  public HybridRowModel add(String column, ConstraintCell cell) {
    getCells().put(column, new HybridCellModel(cell));
    return this;
  }

  public void put(String column, HybridCellModel cell) {
    getCells().put(column, cell);
  }

  public HybridCellModel getDuration() {
    return duration;
  }
}

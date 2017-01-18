package edu.kit.iti.formal.stvs.logic.specification;

import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;

/**
 * Created by csicar on 15.01.17.
 */
public class DfsCyclicReferenceFinder implements CyclicReferenceFinder {
  @Override
  public boolean checkForCyclicReferences(ConstraintSpecification spec) {
    return false;
  }
}

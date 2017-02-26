package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;

import java.io.File;

/**
 * This class is notified when a {@link HybridSpecification} is loaded by
 * {@link ImporterFacade#importFile}.
 */
@FunctionalInterface
public interface ImportHybridSpecificationHandler {
  /**
   * This method needs to be provided by an implementation of
   * {@code ImportHybridSpecificationHandler}. It is called if a {@link HybridSpecification}
   * is loaded.
   * @param hybridSpecification HybridSpecification that was loaded
   */
  void accept(HybridSpecification hybridSpecification);
}

package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;

import java.io.File;

/**
 * An ImportStvsRootModelHandler is notified when a {@link StvsRootModel} is loaded by
 * {@link ImporterFacade#importFile}.
 */
@FunctionalInterface
public interface ImportStvsRootModelHandler {
  /**
   * This method needs to be provided by an implementation of
   * {@code ImportStvsRootModelHandler}. It is called if a {@link StvsRootModel}
   * is loaded.
   * @param model StvsRootModel that was loaded
   */
  void accept(StvsRootModel model);
}

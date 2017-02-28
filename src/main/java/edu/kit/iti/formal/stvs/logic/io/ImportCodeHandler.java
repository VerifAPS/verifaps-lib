package edu.kit.iti.formal.stvs.logic.io;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.config.History;

import java.io.File;

/**
 * An {@code ImportCodeHandler} is notified when {@link Code} is loaded by
 * {@link ImporterFacade.ImportFormat#importFile(File, GlobalConfig, History, ImportHybridSpecificationHandler, ImportStvsRootModelHandler, ImportCodeHandler)}.
 */
@FunctionalInterface
public interface ImportCodeHandler {
  /**
   * This method needs to be provided by an implementation of
   * {@code ImportCodeHandler}. It is called if {@link Code}
   * is loaded.
   * <p>
   *
   * @param code Code that was loaded
   */
  void accept(Code code);
}

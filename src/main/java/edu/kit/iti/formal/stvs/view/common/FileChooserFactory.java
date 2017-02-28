package edu.kit.iti.formal.stvs.view.common;

import javafx.stage.FileChooser;

import java.io.File;
import java.util.HashMap;
import java.util.Map;

/**
 * Factory for creating the appropriate FileChoosers (with the right titles, file extension
 * filters, etc.) for opening and saving files.
 *
 * @author Benjamin Alt
 */
public class FileChooserFactory {

  /**
   * The type of file for which a dialog should be created.
   */
  public enum FileType {
    SPECIFICATION, SESSION, CODE, ANY
  }

  /**
   * The file extension filters corresponding to the different FileTypes.
   */
  private static final Map<FileType, FileChooser.ExtensionFilter> filters;

  /**
   * The String representations of the different FileTypes.
   */
  private static final Map<FileType, String> typeIdentifiers;

  /**
   * Initialize the filters and typeIdentifiers maps.
   */
  static {
    filters = new HashMap<>();
    filters.put(FileType.SPECIFICATION, new FileChooser.ExtensionFilter("Specification files " +
        "(*.xml)", "*.xml"));
    filters.put(FileType.CODE, new FileChooser.ExtensionFilter("Structured Text files (*.st)",
        "*.st"));
    filters.put(FileType.SESSION, new FileChooser.ExtensionFilter("Session files (*.xml)",
        "*.xml"));
    filters.put(FileType.ANY, new FileChooser.ExtensionFilter("ST Verification Studio files (*" +
        ".st, *.xml)", "*.st", "*.xml"));

    typeIdentifiers = new HashMap<>();
    typeIdentifiers.put(FileType.SPECIFICATION, "Specification");
    typeIdentifiers.put(FileType.CODE, "Code");
    typeIdentifiers.put(FileType.SESSION, "Session");
    typeIdentifiers.put(FileType.ANY, "File");
  }

  /**
   * Create a new FileChooser for opening files.
   *
   * @param type       The type of file to open
   * @param workingdir The directory the FileChooser opens initially
   * @return An appropriate FileChooser for opening the given type of file
   */
  public static FileChooser createOpenFileChooser(FileType type, File workingdir) {
    return createFileChooser(workingdir, "Open " + typeIdentifiers.get(type), filters.get(type));
  }

  /**
   * Create a new FileChooser for saving files.
   *
   * @param type       The type of file to save
   * @param workingdir The directory the FileChooser opens initially
   * @return An appropriate FileChooser for saving the given type of file
   */
  public static FileChooser createSaveFileChooser(FileType type, File workingdir) {
    return createFileChooser(workingdir, "Save " + typeIdentifiers.get(type), filters.get(type));
  }

  /**
   * Create a new FileChooser with a given working directory, title and extension filter.
   *
   * @param workingdir The directory the FileChooser opens initially
   * @param title      The FileChooser window title
   * @param filter     The extension filter for the FileChooser
   * @return A FileChooser with the desired characteristics
   */
  public static FileChooser createFileChooser(File workingdir, String title, FileChooser
      .ExtensionFilter filter) {
    FileChooser fileChooser = new FileChooser();
    fileChooser.setTitle(title);
    fileChooser.getExtensionFilters().addAll(filter);
    fileChooser.setInitialDirectory(workingdir);
    return fileChooser;
  }
}

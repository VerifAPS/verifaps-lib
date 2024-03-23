package edu.kit.iti.formal.stvs.model.config;

import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;

import java.io.File;
import java.io.IOException;
import java.util.Collection;

import javafx.collections.FXCollections;
import javafx.collections.ObservableList;

/**
 * Contains information about recently opened code and spec files.
 *
 * @author Benjamin Alt
 */
public class History {

  private static final String AUTOLOAD_HISTORY_FILENAME = "stvs-history.xml";
  public static final int HISTORY_DEPTH = 15;

  private ObservableList<String> filenames;

  public History() {
    filenames = FXCollections.observableArrayList();
  }

  /**
   * Creates a history of recently opened files from the given collection.
   * The Collections' size must be less then or equal to {@link #HISTORY_DEPTH}.
   *
   * @param filenames the most recently opened files.
   * @throws IllegalArgumentException if the given collection is bigger than {@link #HISTORY_DEPTH}
   */
  public History(Collection<String> filenames) {
    this();
    if (filenames.size() > HISTORY_DEPTH) {
      // Don't silently cut off the part of the input collection that doesn't fit
      throw new IllegalArgumentException("List of filenames exceeds history size");
    }
    this.filenames.addAll(filenames);
  }

  /**
   * Get the current file history.
   *
   * @return An ObservableList with the most recently opened filenames.
   */
  public ObservableList<String> getFilenames() {
    return filenames;
  }

  /**
   * Add a filename to the history. If the file already exists inside this history, then
   * it gets reordered to the front of the history. If it is new and the history is full,
   * then the least recently opened file is deleted from the history.
   *
   * @param filename the file to store in the recently opened files history
   */
  public void addFilename(String filename) {
    // Prevent entries from being added twice --> remove and add to the end ("most recent")
    if (filenames.contains(filename)) {
      filenames.remove(filename);
    }
    // Prevent filenames from getting larger than HISTORY_DEPTH
    int excess = filenames.size() - HISTORY_DEPTH + 1;
    if (excess > 0) {
      filenames.remove(0, excess);
    }
    filenames.add(filename);
  }

  /**
   * Loads an xml file from the default history path
   * {@link GlobalConfig#CONFIG_DIRPATH}/{@link #AUTOLOAD_HISTORY_FILENAME}.
   * If this file does not exist or could not be read or parsed, a new history is returned.
   *
   * @return either the history stored at the default path or a new history
   */
  public static History autoloadHistory() {
    File historyFile =
        new File(GlobalConfig.CONFIG_DIRPATH + File.separator + AUTOLOAD_HISTORY_FILENAME);
    try {
      return ImporterFacade.importHistory(historyFile, ImporterFacade.ImportFormat.XML);
    } catch (ImportException e) {
      return new History();
    }
  }

  /**
   * Tries to save this history as xml file to the default history file path
   * {@link GlobalConfig#CONFIG_DIRPATH}/{@link #AUTOLOAD_HISTORY_FILENAME}.
   *
   * @throws IOException if the directories to the default path or the file could not be created
   * @throws ExportException if the history could not be written to the file
   */
  public void autosaveHistory() throws IOException, ExportException {
    File configDir = new File(GlobalConfig.CONFIG_DIRPATH);
    if (!configDir.isDirectory() || !configDir.exists()) {
      if (!configDir.mkdirs()) {
        throw new IOException("Could not create directory: " + configDir);
      }
    }
    File historyFile =
        new File(GlobalConfig.CONFIG_DIRPATH + File.separator + AUTOLOAD_HISTORY_FILENAME);
    ExporterFacade.exportHistory(this, ExporterFacade.ExportFormat.XML, historyFile);
  }

  /**
   * Replaces the contents of this history instance with those of a given history. Preferred over a
   * copy constructor because this method keeps listeners registered on the properties, which will
   * be notified about the changes.
   *
   * @param history The history the contents of which will be copied
   */
  public void setAll(History history) {
    history.getFilenames().forEach(this::addFilename);
  }

  @Override
  public boolean equals(Object o) {
    if (this == o) {
      return true;
    }
    if (o == null || getClass() != o.getClass()) {
      return false;
    }

    History history = (History) o;

    return getFilenames() != null ? getFilenames().equals(history.getFilenames())
        : history.getFilenames() == null;
  }

  @Override
  public int hashCode() {
    return getFilenames() != null ? getFilenames().hashCode() : 0;
  }
}

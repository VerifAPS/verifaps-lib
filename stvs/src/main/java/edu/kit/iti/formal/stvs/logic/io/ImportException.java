package edu.kit.iti.formal.stvs.logic.io;

/**
 * Indicates that an exception occurred during importing.
 *
 * @author Benjamin Alt
 */
public class ImportException extends Exception {
    private String message;

    /**
     * Create a new ImportException with a given error message.
     *
     * @param message The error message
     */
    public ImportException(String message) {
        super(message);
    }

    /**
     * Create a new ImportException from a given Exception (e.g. an exception which was caught
     * during import).
     *
     * @param e The original exception
     */
    public ImportException(Exception e) {
        super(e);
    }

    public ImportException(String s, Exception e) {
        super(s, e);
    }
}

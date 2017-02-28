package edu.kit.iti.formal.stvs.view.common;

import javafx.scene.control.Alert;
import javafx.scene.control.Label;
import javafx.scene.control.TextArea;
import javafx.scene.layout.GridPane;
import javafx.scene.layout.Priority;

import java.io.PrintWriter;
import java.io.StringWriter;

/**
 * Factory for creating alerts.
 *
 * @author Carsten Csiky
 */
public class AlertFactory {

  /**
   * Create an alert for an exception with a default title and description.
   *
   * @param exception The exception for which the alert should be created
   * @return The created alert
   */
  public static Alert createAlert(Throwable exception) {
    return createAlert(exception, "Exception", "An exception occured");
  }

  /**
   * Create an alert for an exception with a custom title and description.
   *
   * @param exception   The exception for which the alert should be created
   * @param title       The title of the alert
   * @param description The description in the alert
   * @return The created alert
   */
  public static Alert createAlert(Throwable exception, String title, String
      description) {
    // Write stack trace to string
    StringWriter sw = new StringWriter();
    PrintWriter pw = new PrintWriter(sw);
    exception.printStackTrace(pw);
    String stackTrace = sw.toString();

    return createAlert(Alert.AlertType.ERROR, title, description, exception.getMessage(),
        stackTrace);
  }

  /**
   * Create an alert with a given type, title, desciption and content text, but without
   * expandable content.
   *
   * @param type        The type of the alert
   * @param title       The title of the alert
   * @param description The description in the alert
   * @param content     The content text for the alert
   * @return The created alert
   */
  public static Alert createAlert(Alert.AlertType type, String title, String description,
                                  String content) {
    return createAlert(type, title, description, content, null);
  }

  /**
   * Create an alert with a given type, title, desciption, content text and expandable content.
   *
   * @param type              The type of the alert
   * @param title             The title of the alert
   * @param description       The description in the alert
   * @param contentText       The content text for the alert
   * @param expandableContent The expandable content in the alert. This parameter may be null
   * @return The created alert
   */
  public static Alert createAlert(Alert.AlertType type, String title, String description,
                                  String contentText, String expandableContent) {
    Alert alert = new Alert(type);
    alert.setTitle(title);
    alert.setHeaderText(description);
    alert.setContentText(contentText);

    TextArea textArea = new TextArea(expandableContent);
    textArea.setEditable(false);
    textArea.setWrapText(true);

    textArea.setMaxWidth(Double.MAX_VALUE);
    textArea.setMaxHeight(Double.MAX_VALUE);
    GridPane.setVgrow(textArea, Priority.ALWAYS);
    GridPane.setHgrow(textArea, Priority.ALWAYS);

    if (expandableContent != null && expandableContent.length() > 0) {
      GridPane expContent = new GridPane();
      expContent.setMaxWidth(Double.MAX_VALUE);
      if (type.equals(Alert.AlertType.ERROR)) {
        Label label = new Label("Stack trace:");
        expContent.add(label, 0, 0);
      }
      expContent.add(textArea, 0, 1);
      alert.getDialogPane().setExpandableContent(expContent);
    }

    if (type.equals(Alert.AlertType.ERROR) && expandableContent != null) {
      System.err.println(contentText);
      System.err.println(expandableContent);
    }

    return alert;
  }
}

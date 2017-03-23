package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.view.ViewUtils;
import javafx.geometry.Pos;
import javafx.scene.Node;
import javafx.scene.control.Button;
import javafx.scene.control.Label;
import javafx.scene.layout.AnchorPane;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Priority;
import javafx.scene.layout.VBox;

/**
 * Created by leonk on 22.03.2017.
 */
public class WizardView extends VBox {

  private final Label titelLabel = new Label();
  private final Label pageNumberLabel = new Label();
  private final Button next = new Button("next");
  private final Button previous = new Button("previous");
  private final AnchorPane content = new AnchorPane();

  public WizardView() {
    super();
    this.getChildren().addAll(createHeader(), content, createFooter());
    this.setVgrow(content, Priority.ALWAYS);
    ViewUtils.setupView(this);
  }

  private AnchorPane createHeader() {
    AnchorPane header = new AnchorPane();
    header.getStyleClass().add("header");
    header.getChildren().addAll(titelLabel, pageNumberLabel);
    titelLabel.getStyleClass().add("title");
    AnchorPane.setLeftAnchor(titelLabel, 10.0);
    AnchorPane.setTopAnchor(titelLabel, 10.0);
    AnchorPane.setRightAnchor(pageNumberLabel, 10.0);
    AnchorPane.setTopAnchor(pageNumberLabel, 10.0);
    return header;
  }

  private AnchorPane createFooter() {
    AnchorPane footer = new AnchorPane();
    footer.getStyleClass().add("footer");
    HBox bottonBox = new HBox(20);
    bottonBox.getChildren().addAll(previous, next);
    footer.getChildren().add(bottonBox);
    AnchorPane.setRightAnchor(bottonBox, 20.0);
    AnchorPane.setTopAnchor(bottonBox, 10.0);
    return footer;
  }

  public Label getTitelLabel() {
    return titelLabel;
  }

  public Label getPageNumberLabel() {
    return pageNumberLabel;
  }

  public Button getNext() {
    return next;
  }

  public Button getPrevious() {
    return previous;
  }

  public void setContent(Node view) {
    content.getChildren().setAll(view);
    AnchorPane.setLeftAnchor(view, 10.0);
    AnchorPane.setRightAnchor(view, 10.0);
    AnchorPane.setTopAnchor(view, 10.0);
    AnchorPane.setBottomAnchor(view, 10.0);
  }
}

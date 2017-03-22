package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.view.Controller;
import javafx.beans.Observable;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.event.ActionEvent;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.stage.Stage;

/**
 * Created by leonk on 22.03.2017.
 */
public class WizardManager implements Controller {

  private final WizardView wizardView;
  private final WizardPage[] wizardPages;
  private final Stage wizardStage;
  private final IntegerProperty pageNumber = new SimpleIntegerProperty(0);

  public WizardManager(WizardPage... wizardPages) {
    if (wizardPages.length < 1) {
      throw new IllegalArgumentException("Cannot create empty wizardView.");
    }
    this.wizardPages = wizardPages;
    wizardView = new WizardView();
    pageNumber.addListener(this::onPageChanged);

    wizardView.getNext().setOnAction(this::next);
    wizardView.getPrevious().setOnAction(this::previous);

    wizardStage = makeStage(wizardView);

    onPageChanged(pageNumber);
  }

  private Stage makeStage(WizardView wizardView) {
    Stage stage = new Stage();
    stage.setScene(new Scene(wizardView));
    return stage;
  }

  private void onPageChanged(Observable observable) {
    int page = pageNumber.get();
    wizardView.getTitelLabel().setText(wizardPages[page].getTitle());
    wizardView.getPageNumberLabel().setText((page + 1) + "/" + wizardPages.length);
    if (page == 0) {
      wizardView.getPrevious().setDisable(true);
    } else {
      wizardView.getPrevious().setDisable(false);
    }
    if (page == wizardPages.length - 1) {
      wizardView.getNext().setOnAction(this::finish);
      wizardView.getNext().setText("finish");
    } else {
      wizardView.getNext().setOnAction(this::next);
      wizardView.getNext().setText("next");
    }
  }

  private void next(ActionEvent event) {
    if (pageNumber.get() + 1 < wizardPages.length) {
      pageNumber.setValue(pageNumber.get() + 1);
    }
  }

  private void previous(ActionEvent event) {
    if (pageNumber.get() > 0) {
      pageNumber.setValue(pageNumber.get() - 1);
    }
  }

  private void finish(ActionEvent event) {
    wizardStage.close();
  }

  public void showAndWait() {
    wizardStage.showAndWait();
  }

  @Override
  public Node getView() {
    return wizardView;
  }
}

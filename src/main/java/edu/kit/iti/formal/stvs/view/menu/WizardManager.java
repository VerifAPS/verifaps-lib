package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.Controller;

import java.io.File;

import javafx.beans.Observable;
import javafx.beans.binding.Bindings;
import javafx.beans.property.IntegerProperty;
import javafx.beans.property.SimpleIntegerProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.collections.FXCollections;
import javafx.collections.ListChangeListener;
import javafx.collections.ObservableList;
import javafx.event.ActionEvent;
import javafx.event.EventHandler;
import javafx.scene.Node;
import javafx.scene.Scene;
import javafx.stage.Stage;
import javafx.stage.WindowEvent;

/**
 * Created by leonk on 22.03.2017.
 */
public class WizardManager implements Controller {

  private final WizardView wizardView;
  private final Stage wizardStage;
  private final IntegerProperty pageNumber = new SimpleIntegerProperty(0);
  private ObservableList<WizardPage> wizardPages = FXCollections.observableArrayList();

  public WizardManager(WizardPage... wizardPages) {
    this.wizardPages.addAll(wizardPages);
    wizardView = new WizardView();
    pageNumber.addListener(this::onPageChanged);

    wizardView.getNext().setOnAction(this::next);
    wizardView.getPrevious().setOnAction(this::previous);

    wizardStage = makeStage(wizardView);
  }

  protected Stage makeStage(WizardView wizardView) {
    Stage stage = new Stage();
    stage.setScene(new Scene(wizardView));
    return stage;
  }

  protected void onPageChanged(Observable observable) {
    int page = pageNumber.get();
    wizardView.getTitelLabel().setText(wizardPages.get(page).getTitle());
    wizardView.getPageNumberLabel().setText((page + 1) + "/" + wizardPages.size());
    wizardView.setContent(wizardPages.get(page));
    if (page == 0) {
      wizardView.getPrevious().setDisable(true);
    } else {
      wizardView.getPrevious().setDisable(false);
    }
    if (page == wizardPages.size() - 1) {
      wizardView.getNext().setOnAction(this::finish);
      wizardView.getNext().setText("finish");
    } else {
      wizardView.getNext().setOnAction(this::next);
      wizardView.getNext().setText("next");
    }
  }

  private void next(ActionEvent event) {
    if (pageNumber.get() + 1 < wizardPages.size()) {
      pageNumber.setValue(pageNumber.get() + 1);
    }
  }

  private void previous(ActionEvent event) {
    if (pageNumber.get() > 0) {
      pageNumber.setValue(pageNumber.get() - 1);
    }
  }

  private void finish(ActionEvent event) {
    wizardStage.fireEvent(
        new WindowEvent(
            wizardStage,
            WindowEvent.WINDOW_CLOSE_REQUEST
        )
    );
  }

  public void showAndWait() {
    if (wizardPages.size() < 1) {
      throw new IllegalArgumentException("Cannot create empty wizardView.");
    }
    wizardPages.addListener(this::illegalChangeListener);
    onPageChanged(pageNumber);
    wizardStage.showAndWait();
    wizardPages.removeListener(this::illegalChangeListener);
    onClose();
  }

  private void illegalChangeListener(ListChangeListener.Change change){
    throw new IllegalStateException("Pages must not be changed while wizard is visible.");
  }

  protected void onClose() {
  }

  public ObservableList<WizardPage> getWizardPages() {
    return wizardPages;
  }

  @Override
  public Node getView() {
    return wizardView;
  }
}

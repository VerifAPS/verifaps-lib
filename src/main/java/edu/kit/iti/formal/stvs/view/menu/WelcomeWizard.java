package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.view.common.AlertFactory;

import java.io.File;
import java.util.Optional;

import javafx.beans.binding.Bindings;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.beans.value.ObservableBooleanValue;
import javafx.scene.control.Alert;
import javafx.scene.control.ButtonType;
import javafx.scene.image.Image;
import javafx.stage.Modality;
import javafx.stage.Stage;
import javafx.stage.WindowEvent;
import org.apache.commons.lang3.SystemUtils;

/**
 * Created by leonk on 22.03.2017.
 */
public class WelcomeWizard extends WizardManager {
  private final GlobalConfig config;
  private final ObservableBooleanValue areAllPathsValid;

  public WelcomeWizard(GlobalConfig config) {
    super();
    this.config = config;
    StringProperty javaPath = new SimpleStringProperty(getOwnJavaPath());
    StringProperty getetaPath = new SimpleStringProperty("");
    config.getetaCommandProperty()
        .bind(Bindings.concat(javaPath, " -jar ", getetaPath, " -c ${code} -t ${spec} -x"));

    WizardFilePathPage java = new WizardFilePathPage("Java",
        "Choose the path to the java executable you would like to use to run the GeTeTa verification engine with.",
        javaPath);
    WizardFilePathPage geteta = new WizardFilePathPage("GeTeTa",
        "Choose the path to the GeTeTa verification engine jar package.", getetaPath,
        "https://formal.iti.kit.edu/weigl/verifaps/geteta/");
    WizardUneditableStringPage getetaCommandPage = new WizardUneditableStringPage("Geteta-Command",
        "The following command will be used to call the GeTeTa verification engine. This command uses placeholders for the code and specification file. This command can be edited in the preferences. If you do not want to tweak the way GeTeTa gets invoked, this command will most likely be sufficient and does not have to be edited manually.\n\nThis command might be wrong if you did not enter the correct paths for the dependencies in the previous pages.",
        config.getetaCommandProperty());
    WizardFilePathPage nuxmv = new WizardFilePathPage("NuXmv",
        "Choose the path to the NuXmv model checker.", config.nuxmvFilenameProperty(),
        "https://es-static.fbk.eu/tools/nuxmv/index.php?n=Download.Download");
    WizardFilePathPage z3 =
        new WizardFilePathPage("Z3", "Choose the path to the Z3 theorem prover executable.",
            config.z3PathProperty(), "https://github.com/Z3Prover/z3/releases");

    getWizardPages().addAll(new WizardWelcomePage(), java, geteta, getetaCommandPage, nuxmv, z3);
    areAllPathsValid = allTrue(java.validProperty(), geteta.validProperty(), nuxmv.validProperty(),
        z3.validProperty());
  }

  private static ObservableBooleanValue allTrue(BooleanProperty... properties) {
    ObservableBooleanValue accu = new SimpleBooleanProperty(true);
    for (int i = 0; i < properties.length; i++) {
      accu = properties[i].and(accu);
    }
    return accu;
  }

  private static String getOwnJavaPath() {
    String extension = "";
    if (SystemUtils.IS_OS_WINDOWS) {
      extension = ".exe";
    }
    return System.getProperty("java.home") + File.separator + "bin" + File.separator + "java"
        + extension;
  }

  @Override
  public void onClose() {
    config.getetaCommandProperty().unbind();
  }

  @Override
  protected Stage makeStage(WizardView wizardView) {
    Stage stage = super.makeStage(wizardView);
    stage.setTitle("STVS - Welcome Wizard");
    stage.getIcons().addAll(new Image(StvsApplication.class.getResourceAsStream("logo_large.png")),
        new Image(StvsApplication.class.getResourceAsStream("logo.png")));
    stage.initModality(Modality.APPLICATION_MODAL);
    stage.setOnCloseRequest(this::closeWarning);
    return stage;
  }

  private void closeWarning(WindowEvent windowEvent) {
    if (areAllPathsValid.get()) {
      return;
    }
    Alert alert = AlertFactory.createAlert(Alert.AlertType.CONFIRMATION, "Unset paths",
        "You are trying to close the wizard, but there are unset paths.",
        "This might leave the application in a state in which not all features are available. You can run the wizard again later by using the menu entry or specify the paths in the preferences. Are you sure to close the wizard now?");
    Optional<ButtonType> returnType = alert.showAndWait();
    if (!ButtonType.OK.equals(returnType.get())) {
      windowEvent.consume();
    }
  }
}

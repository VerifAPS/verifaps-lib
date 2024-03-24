package edu.kit.iti.formal.stvs.view.menu

import edu.kit.iti.formal.stvs.StvsApplication
import edu.kit.iti.formal.stvs.model.config.GlobalConfig
import edu.kit.iti.formal.stvs.view.common.AlertFactory
import javafx.beans.binding.Bindings
import javafx.beans.property.BooleanProperty
import javafx.beans.property.SimpleBooleanProperty
import javafx.beans.property.SimpleStringProperty
import javafx.beans.property.StringProperty
import javafx.beans.value.ObservableBooleanValue
import javafx.event.EventHandler
import javafx.scene.control.Alert.AlertType
import javafx.scene.control.ButtonType
import javafx.scene.image.Image
import javafx.stage.Modality
import javafx.stage.Stage
import javafx.stage.WindowEvent
import org.apache.commons.lang3.SystemUtils
import java.io.File

/**
 * Created by leonk on 22.03.2017.
 */
class WelcomeWizard(private val config: GlobalConfig) : WizardManager() {
    private val areAllPathsValid: ObservableBooleanValue

    init {
        val javaPath: StringProperty = SimpleStringProperty(ownJavaPath)
        val getetaPath: StringProperty = SimpleStringProperty("")
        config.getetaCommandProperty
            .bind(Bindings.concat(javaPath, " -jar ", getetaPath, " -c \${code} -t \${spec} -x"))

        val java = WizardFilePathPage(
            "Java",
            "Choose the path to the java executable you would like to use to run the GeTeTa verification engine with.",
            javaPath
        )
        val geteta = WizardFilePathPage(
            "GeTeTa",
            "Choose the path to the GeTeTa verification engine jar package.", getetaPath,
            "https://formal.iti.kit.edu/weigl/verifaps/geteta/"
        )
        val getetaCommandPage = WizardUneditableStringPage(
            "Geteta-Command",
            "The following command will be used to call the GeTeTa verification engine. This command uses placeholders for the code and specification file. This command can be edited in the preferences. If you do not want to tweak the way GeTeTa gets invoked, this command will most likely be sufficient and does not have to be edited manually.\n\nThis command might be wrong if you did not enter the correct paths for the dependencies in the previous pages.",
            config.getetaCommandProperty
        )
        val nuxmv = WizardFilePathPage(
            "NuXmv",
            "Choose the path to the NuXmv model checker.", config.nuxmvFilenameProperty,
            "https://es-static.fbk.eu/tools/nuxmv/index.php?n=Download.Download"
        )
        val z3 =
            WizardFilePathPage(
                "Z3", "Choose the path to the Z3 theorem prover executable.",
                config.z3PathProperty, "https://github.com/Z3Prover/z3/releases"
            )

        wizardPages.addAll(WizardWelcomePage(), java, geteta, getetaCommandPage, nuxmv, z3)
        areAllPathsValid = allTrue(
            java.validProperty(), geteta.validProperty(), nuxmv.validProperty(),
            z3.validProperty()
        )
    }

    public override fun onClose() {
        config.getetaCommandProperty.unbind()
    }

    override fun makeStage(wizardView: WizardView?): Stage {
        val stage = super.makeStage(wizardView)
        stage!!.title = "STVS - Welcome Wizard"
        stage.icons.addAll(
            Image(StvsApplication::class.java.getResourceAsStream("logo_large.png")),
            Image(StvsApplication::class.java.getResourceAsStream("logo.png"))
        )
        stage.initModality(Modality.APPLICATION_MODAL)
        stage.onCloseRequest = EventHandler { windowEvent: WindowEvent -> this.closeWarning(windowEvent) }
        return stage
    }

    private fun closeWarning(windowEvent: WindowEvent) {
        if (areAllPathsValid.get()) {
            return
        }
        val alert = AlertFactory.createAlert(
            AlertType.CONFIRMATION, "Unset paths",
            "You are trying to close the wizard, but there are unset paths.",
            "This might leave the application in a state in which not all features are available. You can run the wizard again later by using the menu entry or specify the paths in the preferences. Are you sure to close the wizard now?"
        )
        val returnType = alert.showAndWait()
        if (ButtonType.OK != returnType.get()) {
            windowEvent.consume()
        }
    }

    companion object {
        private fun allTrue(vararg properties: BooleanProperty): ObservableBooleanValue {
            var accu: ObservableBooleanValue = SimpleBooleanProperty(true)
            for (i in properties.indices) {
                accu = properties[i].and(accu)
            }
            return accu
        }

        private val ownJavaPath: String
            get() {
                var extension = ""
                if (SystemUtils.IS_OS_WINDOWS) {
                    extension = ".exe"
                }
                return (System.getProperty("java.home") + File.separator + "bin" + File.separator + "java"
                        + extension)
            }
    }
}

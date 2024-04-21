package edu.kit.iti.formal.stvs.view.common

import org.junit.jupiter.api.Tag

import edu.kit.iti.formal.stvs.view.common.AlertFactory.createAlert
import javafx.application.Application
import javafx.stage.Stage

/**
 * Created by csicar on 01.02.17.
 */
@Tag("demo")
class ErrorMessageDialogDemo : Application() {
    @Throws(Exception::class)
    override fun start(stage: Stage) {
        createAlert(Exception("Test")).showAndWait()
    }
}
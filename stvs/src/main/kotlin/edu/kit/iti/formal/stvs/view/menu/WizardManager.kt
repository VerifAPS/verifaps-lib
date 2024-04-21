package edu.kit.iti.formal.stvs.view.menu

import edu.kit.iti.formal.stvs.view.Controller
import javafx.beans.Observable
import javafx.beans.property.IntegerProperty
import javafx.beans.property.SimpleIntegerProperty
import javafx.collections.FXCollections
import javafx.collections.ListChangeListener
import javafx.collections.ObservableList
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.Node
import javafx.scene.Scene
import javafx.stage.Stage
import javafx.stage.WindowEvent

/**
 * Created by leonk on 22.03.2017.
 */
open class WizardManager(vararg wizardPages: WizardPage?) : Controller {
    private val wizardView: WizardView
    private val wizardStage: Stage?
    private val pageNumber: IntegerProperty = SimpleIntegerProperty(0)
    val wizardPages: ObservableList<WizardPage?> = FXCollections.observableArrayList()

    init {
        this.wizardPages.addAll(*wizardPages)
        wizardView = WizardView()
        pageNumber.addListener { observable: Observable? -> this.onPageChanged(observable) }

        wizardView.next.onAction = EventHandler { event: ActionEvent -> this.next(event) }
        wizardView.previous.onAction = EventHandler { event: ActionEvent -> this.previous(event) }

        wizardStage = makeStage(wizardView)
        wizardStage!!.width = wizardView.width
        wizardStage.height = wizardView.height
        wizardStage.x = 0.0
        wizardStage.y = 0.0
    }

    protected open fun makeStage(wizardView: WizardView?): Stage? {
        val stage = Stage()
        stage.scene = Scene(wizardView)
        return stage
    }

    protected fun onPageChanged(observable: Observable?) {
        val page = pageNumber.get()
        wizardView.titleLabel.text = wizardPages[page]!!.title
        wizardView.pageNumberLabel.text = (page + 1).toString() + "/" + wizardPages.size
        wizardView.setContent(wizardPages[page])
        if (page == 0) {
            wizardView.previous.isDisable = true
        } else {
            wizardView.previous.isDisable = false
        }
        if (page == wizardPages.size - 1) {
            wizardView.next.onAction = EventHandler { event: ActionEvent -> this.finish(event) }
            wizardView.next.text = "Finish"
        } else {
            wizardView.next.onAction = EventHandler { event: ActionEvent -> this.next(event) }
            wizardView.next.text = "Next"
        }
    }

    private fun next(event: ActionEvent) {
        if (pageNumber.get() + 1 < wizardPages.size) {
            pageNumber.value = pageNumber.get() + 1
        }
    }

    private fun previous(event: ActionEvent) {
        if (pageNumber.get() > 0) {
            pageNumber.value = pageNumber.get() - 1
        }
    }

    private fun finish(event: ActionEvent) {
        wizardStage!!.fireEvent(
            WindowEvent(
                wizardStage,
                WindowEvent.WINDOW_CLOSE_REQUEST
            )
        )
    }

    fun showAndWait() {
        require(wizardPages.size >= 1) { "Cannot create empty wizardView." }
        wizardPages.addListener(ListChangeListener { change -> this.illegalChangeListener(change) })
        onPageChanged(pageNumber)
        wizardStage!!.showAndWait()
        wizardPages.removeListener(ListChangeListener { change -> this.illegalChangeListener(change) })
        onClose()
    }

    private fun illegalChangeListener(change: ListChangeListener.Change<*>) {
        throw IllegalStateException("Pages must not be changed while wizard is visible.")
    }

    protected open fun onClose() {
    }

    override val view: Node
        get() = wizardView
}

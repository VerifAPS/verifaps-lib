package edu.kit.iti.formal.stvs.view.menu

import edu.kit.iti.formal.stvs.view.ViewUtils
import javafx.scene.Node
import javafx.scene.control.*
import javafx.scene.layout.*

/**
 * Created by leonk on 22.03.2017.
 */
class WizardView : VBox() {
    val titleLabel: Label = Label()
    val pageNumberLabel: Label = Label()
    val next: Button = Button("Next")
    val previous: Button = Button("Previous")
    private val content = AnchorPane()

    init {
        children.addAll(createHeader(), content, createFooter())
        setVgrow(content, Priority.ALWAYS)
        ViewUtils.setupView(this)
    }

    private fun createHeader(): AnchorPane {
        val header = AnchorPane()
        header.styleClass.add("header")
        header.children.addAll(titleLabel, pageNumberLabel)
        titleLabel.styleClass.add("title")
        AnchorPane.setLeftAnchor(titleLabel, 10.0)
        AnchorPane.setTopAnchor(titleLabel, 10.0)
        AnchorPane.setRightAnchor(pageNumberLabel, 10.0)
        AnchorPane.setTopAnchor(pageNumberLabel, 10.0)
        return header
    }

    private fun createFooter(): AnchorPane {
        val footer = AnchorPane()
        footer.styleClass.add("footer")
        val bottonBox = HBox(20.0)
        bottonBox.children.addAll(previous, next)
        footer.children.add(bottonBox)
        AnchorPane.setRightAnchor(bottonBox, 20.0)
        AnchorPane.setTopAnchor(bottonBox, 10.0)
        AnchorPane.setBottomAnchor(bottonBox, 10.0)
        return footer
    }

    fun setContent(view: Node?) {
        content.children.setAll(view)
        AnchorPane.setLeftAnchor(view, 10.0)
        AnchorPane.setRightAnchor(view, 10.0)
        AnchorPane.setTopAnchor(view, 10.0)
        AnchorPane.setBottomAnchor(view, 10.0)
    }
}

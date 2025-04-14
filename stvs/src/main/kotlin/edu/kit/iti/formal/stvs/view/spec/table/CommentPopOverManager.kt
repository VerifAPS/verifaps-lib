package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.model.table.Commentable
import javafx.event.EventHandler
import javafx.scene.Node

class CommentPopOverManager(
    private val commentable: Commentable,
    private val editable: Boolean,
    private val node: Node?,
    private val x: Double = 0.0,
    private val y: Double = 0.0
) {
    init {
        val commentPopOver = CommentPopOver()
        commentPopOver.show(node)
        commentPopOver.textArea.text = commentable.comment
        commentPopOver.saveButton.onAction = EventHandler { _ ->
            commentable.comment = commentPopOver.textArea.text
            commentPopOver.hide()
        }
    }
}

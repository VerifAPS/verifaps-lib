package edu.kit.iti.formal.stvs.view.spec.table

import edu.kit.iti.formal.stvs.model.table.Commentable
import javafx.event.ActionEvent
import javafx.event.EventHandler
import javafx.scene.Node

class CommentPopOverManager @JvmOverloads constructor(
    commentable: Commentable?,
    editable: Boolean,
    node: Node?,
    x: Double = 0.0,
    y: Double = 0.0
) {
    private val commentable: Commentable?
    private val editable: Boolean
    private val commentPopOver: CommentPopOver

    init {
        if (node == null) {
            throw NullPointerException("Node node cannot be null")
        }
        this.commentable = commentable
        this.editable = editable
        this.commentPopOver = CommentPopOver()
        commentPopOver.show(node)
        commentPopOver.textArea.text = commentable!!.comment
        commentPopOver.saveButton.onAction = EventHandler { actionEvent: ActionEvent? ->
            commentable.comment = commentPopOver.textArea.text
            commentPopOver.hide()
        }
    }
}

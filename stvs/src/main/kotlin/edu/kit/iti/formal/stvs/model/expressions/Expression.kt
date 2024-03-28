package edu.kit.iti.formal.stvs.model.expressions

import edu.kit.iti.formal.stvs.model.common.IoVariable
import edu.kit.iti.formal.stvs.model.table.StringReadable
import javafx.beans.property.*

/**
 *
 * The abstract super class for all Expressions.
 *
 *
 * This type does not contain all information the source expression string had. That means you
 * can't get back the expression string from this Expression. For example an expression <tt>= 3</tt>
 * in a column for [IoVariable] <tt>X</tt> is parsed as <tt>X = 3</tt> by the
 * [ExpressionParser].
 *
 *
 * The only ability all Expressions currently share is getting visited.
 *
 * @author Philipp
 */
abstract class Expression : StringReadable {
    /**
     *
     * Find out what subclass of Expression this is by supplying a visitor.
     *
     * @param visitor an [ExpressionVisitor] for handling different cases of Expression
     * sublcasses
     * @param <R> the return type that the expression visitor produces
     * @return the return value that the expression visitor produced
    </R> */
    abstract fun <R> takeVisitor(visitor: ExpressionVisitor<R>): R

    override val stringRepresentationProperty = SimpleStringProperty()
}

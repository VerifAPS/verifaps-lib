package edu.kit.iti.formal.util

import java.io.StringWriter
import java.io.Writer
import java.util.*

interface Semantic<T> {
    fun open(writer: SemanticCodeWriter<T>, vararg clazz: T)
    fun close(writer: SemanticCodeWriter<T>, vararg clazz: T)
}

/**
 * Semantic CodeWriter allows given semantic classes to printed text.
 * @author weigla (23.10.2018)
 * @version 1
 */
open class SemanticCodeWriter<T>(
        var semantic: Semantic<T>,
        var stream: Writer = StringWriter())
    : Appendable by stream {

    protected var identation = 0
    var identationChar: String = " "
    var identationFactor: Int = 4

    private fun write(x: Any): SemanticCodeWriter<T> {
        stream.write(x.toString())
        return this
    }

    fun appendIdent(): SemanticCodeWriter<T> {
        for (i in 0 until identationFactor * identation) {
            stream.write(identationChar)
        }
        return this
    }

    operator fun inc() = increaseIndent()
    fun increaseIndent(): SemanticCodeWriter<T> {
        identation++
        return this
    }

    operator fun dec() = decreaseIndent()
    fun decreaseIndent(): SemanticCodeWriter<T> {
        identation = Math.max(identation - 1, 0)
        return this
    }

    fun nl(): SemanticCodeWriter<T> {
        write("\n")
        appendIdent()
        return this
    }

    fun println(arg: String): SemanticCodeWriter<T> = print(arg).nl()
    fun print(arg: String): SemanticCodeWriter<T> = write(arg)
    fun printf(fmt: String, vararg args: Any): SemanticCodeWriter<T> {
        stream.write(String.format(fmt, *args))
        return this
    }

    fun println(vararg clazz: T, arg: String): SemanticCodeWriter<T> {
        semantic.open(this, *clazz)
        print(arg).nl()
        semantic.close(this, *clazz)
        return this
    }

    fun print(vararg clazz: T, arg: String): SemanticCodeWriter<T> = write(arg)
    fun printf(clazz: T, fmt: String, vararg args: Any): SemanticCodeWriter<T> {
        stream.write(String.format(fmt, *args))
        return this
    }


    fun print(vararg args: Any): SemanticCodeWriter<T> {
        args.forEach { write(it.toString()) }
        return this
    }


    fun appendReformat(text: String): SemanticCodeWriter<T> {
        text.splitToSequence('\n').forEach { nl().printf(it) }
        return this
    }

    fun block(text: String = "", nl: Boolean = false,
              function: SemanticCodeWriter<T>.() -> Unit): SemanticCodeWriter<T> {
        printf(text)
        if (nl) nl()
        increaseIndent()
        function()
        decreaseIndent()
        if (nl) nl()
        return this
    }

    fun cblock(head: String, tail: String,
               function: SemanticCodeWriter<T>.() -> Unit): SemanticCodeWriter<T> {
        printf(head)
        increaseIndent()
        nl()
        function()
        decreaseIndent()
        nl()
        printf(tail)
        return this
    }

    val stack = Stack<Array<out T>>()
    fun open(vararg clazz: T): SemanticCodeWriter<T> {
        semantic.open(this, *clazz)
        stack.push(clazz)
        return this
    }

    fun semblock(vararg clazz: T, function: () -> Unit): SemanticCodeWriter<T> {
        semantic.open(this, *clazz)
        function()
        semantic.close(this, *clazz)
        return this
    }

    fun close(): SemanticCodeWriter<T> {
        semantic.close(this, *stack.pop())
        return this
    }
}

enum class SemanticClasses {
    KEYWORD, STATEMENT, CASE_INTEGER_CONDITION, CASE_ENUM_CONDITION,
    OPERATOR, BINARY_EXPRESSION, ASSIGNMENT, TYPE_DECL_ENUM, TYPE_NAME,
    REPEAT, WHILE, UNARY_EXPRESSION, TYPE_DECL, CASE_STATEMENT,
    VARIABLE, SUBSCRIPT, STATEMENT_BLOCK, PROGRAM, VALUE, EXPRESSION_LIST,
    SEPARATOR, FUNC_CALL, FOR, FB, IFSTATEMENT, FB_CALL,
    CASE, TYPE_DECL_SIMPLE, VARIABLES_DEFINITION, COMMENT, TYPE_DECL_DECL,
    VARIABLES_DEFINITIONS, SPECIAL_VARIABLE, CONSTANT, ERROR
}

class DefaultHtmlSemantic : Semantic<SemanticClasses> {
    override fun open(writer: SemanticCodeWriter<SemanticClasses>, vararg clazz: SemanticClasses) {
        writer.print("<span class='${clazz.joinToString(",") { it.name }}'>")
    }

    override fun close(writer: SemanticCodeWriter<SemanticClasses>, vararg clazz: SemanticClasses) {
        writer.print("</span>")
    }
}
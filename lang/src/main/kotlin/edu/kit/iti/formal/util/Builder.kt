package edu.kit.iti.formal.util

import edu.kit.iti.formal.automation.st.PPStructuredTextPrinter
import io.github.wadoon.pp.Document
import io.github.wadoon.pp.break1
import io.github.wadoon.pp.breakOrSpaces
import io.github.wadoon.pp.concat
import io.github.wadoon.pp.hardline
import io.github.wadoon.pp.nest
import io.github.wadoon.pp.space
import io.github.wadoon.pp.string

class Builder {
    private val indentation: Int = 4
    var doc: Document = Document.Empty

    fun append(doc2: Document): Builder {
        doc = concat(doc, doc2)
        return this
    }

    fun keyword(s: String) = append(string(s))
    fun space() = append(space)

    operator fun Document.unaryPlus() = append(this)
    operator fun String.unaryPlus() = append(string(this))
    operator fun Char.unaryPlus() = this.toString().unaryPlus()

    fun indent(fn: Builder.() -> Unit): Builder {
        val b = Builder()
        fn(b)
        return append(nest(indentation,  b.doc))
    }

    fun nl(): Builder {
        +hardline
        return this
    }

    fun appendIdent() = this

    fun write(s: String): Builder {
        s.unaryPlus()
        return this
    }
    
    fun printf(s: String): Builder {
        s.unaryPlus()
        return this
    }

    fun comment(fmt: String, vararg args: Any): Builder = fmt.format(args).unaryPlus()
}
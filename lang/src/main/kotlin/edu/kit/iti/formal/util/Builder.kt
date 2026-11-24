/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.util

import io.github.wadoon.pp.Document
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
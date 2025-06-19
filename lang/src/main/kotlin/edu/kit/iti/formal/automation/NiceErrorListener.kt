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
package edu.kit.iti.formal.automation

/*-
 * #%L
 * jpox
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import org.antlr.v4.runtime.*
import kotlin.math.max

/**
 * Created by weigl on 10/07/14.
 */
class NiceErrorListener(private val content: String) : BaseErrorListener() {

    override fun syntaxError(
        recognizer: Recognizer<*, *>?,
        offendingSymbol: Any?,
        line: Int,
        charPositionInLine: Int,
        msg: String?,
        e: RecognitionException?,
    ) {
        val lines = content.split("\n".toRegex()).dropLastWhile { it.isEmpty() }.toList()
        System.err.println("$line@$charPositionInLine")
        System.err.println((recognizer as Parser).ruleInvocationStack)

        var cur: RuleContext? = e!!.ctx
        while (cur != null) {
            System.err.println(
                cur.depth().toString() + " >> " + recognizer.ruleNames[
                    cur
                        .ruleIndex,
                ] + " : " + cur.text,
            )
            cur = cur.parent
        }

        System.err.format(
            "ERROR: line %d:%d: %s%n",
            line,
            charPositionInLine,
            msg,
        )
        for (i in Math.max(0, line - 2) until lines.size) {
            System.err.println(lines[i])

            if (i + 1 == line) {
                System.err.print(">")
                for (j in 0 until max(0, charPositionInLine - 1)) {
                    print(' ')
                }
                println("^ " + msg!!)
                break
            }
        }
        System.err.format("==============================\n")
    }
}
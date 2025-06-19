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

import java.util.*

/* Copyright (c) 2012 Kevin L. Stern
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
 * SOFTWARE.
 */

/**
 * The Damerau-Levenshtein Algorithm is an extension to the Levenshtein
 * Algorithm which solves the edit distance problem between a source string and
 * a target string with the following operations:
 *
 *
 *  * Character Insertion
 *  * Character Deletion
 *  * Character Replacement
 *  * Adjacent Character Swap
 *
 *
 * Note that the adjacent character swap operation is an edit that may be
 * applied when two adjacent characters in the source string match two adjacent
 * characters in the target string, but in reverse order, rather than a general
 * allowance for adjacent character swaps.
 *
 *
 *
 * This implementation allows the client to specify the costs of the various
 * edit operations with the restriction that the cost of two swap operations
 * must not be less than the cost of a delete operation followed by an insert
 * operation. This restriction is required to preclude two swaps involving the
 * same character being required for optimality which, in turn, enables a fast
 * dynamic programming solution.
 *
 *
 *
 * The running time of the Damerau-Levenshtein algorithm is O(n*m) where n is
 * the length of the source string and m is the length of the target string.
 * This implementation consumes O(n*m) space.
 *
 * @author Kevin L. Stern
 */
fun dlevenshtein(
    source: String,
    target: String,
    deleteCost: Int = 1,
    insertCost: Int = 1,
    replaceCost: Int = 1,
    swapCost: Int = 1,
): Int {
    /*
     * Required to facilitate the premise to the algorithm that two swaps of the
     * same character are never required for optimality.
     */
    if (2 * swapCost < insertCost + deleteCost) {
        throw IllegalArgumentException("Unsupported cost assignment")
    }
    if (source.length == 0) {
        return target.length * insertCost
    }
    if (target.length == 0) {
        return source.length * deleteCost
    }
    val table = Array(source.length) { IntArray(target.length) }
    val sourceIndexByCharacter = HashMap<Char, Int>()
    if (source[0] != target[0]) {
        table[0][0] = Math.min(replaceCost, deleteCost + insertCost)
    }
    sourceIndexByCharacter[source[0]] = 0
    for (i in 1 until source.length) {
        val deleteDistance = table[i - 1][0] + deleteCost
        val insertDistance = (i + 1) * deleteCost + insertCost
        val matchDistance = i * deleteCost + if (source[i] == target[0]) 0 else replaceCost
        table[i][0] = Math.min(
            Math.min(deleteDistance, insertDistance),
            matchDistance,
        )
    }
    for (j in 1 until target.length) {
        val deleteDistance = (j + 1) * insertCost + deleteCost
        val insertDistance = table[0][j - 1] + insertCost
        val matchDistance = j * insertCost + if (source[0] == target[j]) 0 else replaceCost
        table[0][j] = Math.min(
            Math.min(deleteDistance, insertDistance),
            matchDistance,
        )
    }
    for (i in 1 until source.length) {
        var maxSourceLetterMatchIndex = if (source[i] == target[0]) {
            0
        } else {
            -1
        }
        for (j in 1 until target.length) {
            val candidateSwapIndex = sourceIndexByCharacter[target[j]]
            val jSwap = maxSourceLetterMatchIndex
            val deleteDistance = table[i - 1][j] + deleteCost
            val insertDistance = table[i][j - 1] + insertCost
            var matchDistance = table[i - 1][j - 1]
            if (source[i] != target[j]) {
                matchDistance += replaceCost
            } else {
                maxSourceLetterMatchIndex = j
            }
            val swapDistance: Int
            if (candidateSwapIndex != null && jSwap != -1) {
                val preSwapCost: Int
                if (candidateSwapIndex == 0 && jSwap == 0) {
                    preSwapCost = 0
                } else {
                    preSwapCost = table[Math.max(0, candidateSwapIndex - 1)][Math.max(0, jSwap - 1)]
                }
                swapDistance = (
                    preSwapCost + (i - candidateSwapIndex - 1) * deleteCost +
                        (j - jSwap - 1) * insertCost + swapCost
                    )
            } else {
                swapDistance = Integer.MAX_VALUE
            }
            table[i][j] = Math.min(
                Math.min(
                    Math
                        .min(deleteDistance, insertDistance),
                    matchDistance,
                ),
                swapDistance,
            )
        }
        sourceIndexByCharacter[source[i]] = i
    }
    return table[source.length - 1][target.length - 1]
}
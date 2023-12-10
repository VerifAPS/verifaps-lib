/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 */
package edu.kit.iti.formal.automation.testtables.exception


import edu.kit.iti.formal.smv.ast.SMVModule
import edu.kit.iti.formal.smv.ast.SVariable
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
class SpecificationInterfaceMisMatchException : GetetaException {
    constructor() : super() {}

    constructor(message: String) : super(message) {}

    constructor(message: String, cause: Throwable) : super(message, cause) {}

    constructor(cause: Throwable) : super(cause) {}

    protected constructor(message: String, cause: Throwable,
                          enableSuppression: Boolean,
                          writableStackTrace: Boolean) : super(message, cause, enableSuppression, writableStackTrace) {
    }

    constructor(code: SMVModule, v: SVariable) :
            super(String.format("Could not find variable '%s' in module: %s. Candidates would be: %s",
                    v.name, code.name, SpecificationInterfaceMisMatchException.candidates(v.name, code)
            ))

    companion object {

        private fun candidates(name: String, code: SMVModule): String {
            val vars = code.stateVars + code.inputVars + code.frozenVars;
            val candidates = vars.map { it.name }
            val best = candidates(name, candidates)
            return best.take(3).reduce { a, b -> "$a, $b" }
        }

        private fun candidates(name: String, code: List<String>): Collection<String> {
            val heap = PriorityQueue(
                    LevensteinCaseInsensitiveComparator(name))
            heap.addAll(code)
            return heap
        }

        internal class LevensteinCaseInsensitiveComparator(name: String) : Comparator<String> {
            private val reference: String
            var computed: MutableMap<String, Int> = HashMap()

            init {
                this.reference = name.lowercase(Locale.getDefault())
            }


            override fun compare(o1: String, o2: String): Int {
                val level1 = getLevenstheinToRef(o1)
                val level2 = getLevenstheinToRef(o2)
                return Integer.compare(level1, level2)
            }

            private fun getLevenstheinToRef(o1: String): Int {
                val k = o1.lowercase(Locale.getDefault())
                return (computed as java.util.Map<String, Int>).computeIfAbsent(k) { s ->
                    levenshteinDistance(
                        reference,
                        s
                    )
                }
            }

            /**
             * from https://en.wikibooks.org/wiki/Algorithm_Implementation/Strings/Levenshtein_distance#Java
             *
             * @param lhs
             * @param rhs
             * @return
             */
            fun levenshteinDistance(lhs: CharSequence, rhs: CharSequence): Int {
                val len0 = lhs.length + 1
                val len1 = rhs.length + 1

                // the array of distances
                var cost = IntArray(len0)
                var newcost = IntArray(len0)

                // initial cost of skipping prefix in String s0
                for (i in 0 until len0) cost[i] = i

                // dynamically computing the array of distances

                // transformation cost for each letter in s1
                for (j in 1 until len1) {
                    // initial cost of skipping prefix in String s1
                    newcost[0] = j

                    // transformation cost for each letter in s0
                    for (i in 1 until len0) {
                        // matching current letters in both strings
                        val match = if (lhs[i - 1] == rhs[j - 1]) 0 else 1

                        // computing cost for each transformation
                        val cost_replace = cost[i - 1] + match
                        val cost_insert = cost[i] + 1
                        val cost_delete = newcost[i - 1] + 1

                        // fwdprogress minimum cost
                        newcost[i] = Math.min(Math.min(cost_insert, cost_delete), cost_replace)
                    }

                    // swap cost/newcost arrays
                    val swap = cost
                    cost = newcost
                    newcost = swap
                }

                // the distance is the cost for transforming all letters in both strings
                return cost[len0 - 1]
            }
        }
    }
}

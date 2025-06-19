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
package edu.kit.iti.formal.automation.absint

/**
 *
 * @author Alexander Weigl
 * @version 1 (20.11.18)
 */
abstract class Lattice<T>(val elements: Set<T>) {

    open fun cup(seq: Collection<T>): T = seq.reduce(this::cup)

    abstract fun cup(a: T, b: T): T

    open fun cap(seq: Collection<T>): T = seq.reduce(this::cap)

    abstract fun cap(a: T, b: T): T
}

enum class TaintEq { EQUAL, NOT_EQUAL }

class TaintEqLattice : Lattice<TaintEq>(TaintEq.entries.toSet()) {
    override fun cup(a: TaintEq, b: TaintEq): TaintEq = when {
        a == TaintEq.NOT_EQUAL || b == TaintEq.NOT_EQUAL ->
            TaintEq.NOT_EQUAL
        else ->
            TaintEq.EQUAL
    }

    override fun cap(a: TaintEq, b: TaintEq): TaintEq = when {
        a == TaintEq.EQUAL || b == TaintEq.EQUAL ->
            TaintEq.EQUAL
        else ->
            TaintEq.NOT_EQUAL
    }
}
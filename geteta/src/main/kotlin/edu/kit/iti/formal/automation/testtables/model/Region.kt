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
package edu.kit.iti.formal.automation.testtables.model


import java.util.*

/**
 * created on 10.12.16.
 *
 * @author Alexander Weigl
 * @version 1
 */
class Region(id: String) : TableNode(id) {
    override var children: MutableList<TableNode> = ArrayList()
        set(children) {
            field = this.children
        }

    override val isLeaf: Boolean
        get() = false

    override val automataStates: List<State.AutomatonState> by lazy {
        val seq = ArrayList<State.AutomatonState>(100)
        flat().forEach { state -> seq.addAll(state.automataStates) }
        seq
    }

    constructor(id: Int) : this("" + id) {}

    /**
     * @return
     */
    override fun count(): Int {
        return this.children.sumBy { it.count() }
    }

    /**
     * @return
     */
    override fun flat(): List<State> {
        return this.children.flatMap { a -> a.flat() }
    }

    override fun depth(): Int {
        val c = (this.children.maxBy { it.depth() }?.depth() ?: 0)
        return 1 + c
    }
}
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


import lombok.Data

/**
 *
 * Created on 10.12.16
 *
 * @author Alexander Weigl
 */
@Data
class Duration {

    private val lower: Int
    private val upper: Int

    /**
     * returns true, iff the step can be applied arbitrary often (no upper bound)
     *
     * @return
     */
    val isUnbounded: Boolean
        get() = upper <= -1

    /**
     * returns true, iff the step is applied only once
     *
     * @return
     */
    val isOneStep: Boolean
        get() = fixedStep() && upper == 1

    /**
     * returns true, if the step can be overjumped directly
     *
     * @return
     */
    val isSkippable: Boolean
        get() = lower == 0


    /**
     *
     */
    val isDeterministicWait: Boolean
        get() = equals(DET_WAIT)

    val isOmega: Boolean
        get() = equals(OMEGA)

    /**
     *
     * @return true iff this row can be applied more than once.
     */
    val isRepeatable: Boolean
        get() = upper > 1 || upper == OMEGA.upper || upper == DET_WAIT.upper

    /**
     * @return
     */
    val bound: Int
        get() = Math.max(1, Math.max(lower, upper))

    constructor() {
        assert(invariant())
    }

    constructor(l: Int, u: Int) {
        lower = l
        upper = u
        assert(invariant())
    }

    fun invariant(): Boolean {
        return true//(upper >= lower || isUnbounded()) && lower >= 0;
    }

    /**
     * returns the maximum integer interval border.
     *
     *
     *
     * Useful for the integer width needed to store the clock value
     *
     * @return
     */
    fun maxCounterValue(): Int {
        return bound + 1
    }

    /**
     * Returns true if the duration is a singleton interval
     *
     * @return
     */
    fun fixedStep(): Boolean {
        return upper == lower
    }

    /**
     * checks if the given integer lies within the duration
     *
     * @param cycles
     * @return
     */
    operator fun contains(cycles: Int): Boolean {
        return lower <= cycles && (isUnbounded || cycles <= upper)
    }

    companion object {
        val OMEGA = Duration(-2, -2)
        val DET_WAIT = Duration(-1, -1)
    }
}

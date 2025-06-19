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
package edu.kit.iti.formal.automation.testtables.model

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
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
 * #L%
 */

/**
 * @author Alexander Weigl
 * @version 1 (03.05.17)
 */
enum class VerificationTechnique private constructor(vararg commands: String) {
    IC3(
        "read_model",
        "flatten_hierarchy",
        "show_vars",
        "encode_variables",
        "build_boolean_model",
        "check_invar_ic3",
        "quit",
    ),

    LTL(
        "read_model",
        "flatten_hierarchy",
        "show_vars",
        "encode_variables",
        "build_model",
        "check_ltlspec",
        "quit",
    ),

    INVAR(
        "read_model",
        "flatten_hierarchy",
        "show_vars",
        "encode_variables",
        "build_model",
        "check_invar",
        "quit",
    ),

    BMC(
        "read_model",
        "flatten_hierarchy",
        "show_vars",
        "encode_variables",
        "build_boolean_model",
        "check_invar_bmc -a een-sorrensen",
        "quit",
    ),
    ;

    val commands: Array<String> = commands as Array<String>
}

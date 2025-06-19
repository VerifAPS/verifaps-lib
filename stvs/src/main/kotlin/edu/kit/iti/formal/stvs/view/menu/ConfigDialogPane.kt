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
package edu.kit.iti.formal.stvs.view.menu

import edu.kit.iti.formal.stvs.view.ViewUtils
import edu.kit.iti.formal.stvs.view.common.FileSelectionField
import edu.kit.iti.formal.stvs.view.common.PositiveIntegerInputField
import javafx.geometry.Insets
import javafx.scene.control.*
import javafx.scene.layout.GridPane

/**
 * The view for a config dialog. Includes numerous text fields, checkboxes and number text fields
 * that match the fields of a [edu.kit.iti.formal.stvs.model.config.GlobalConfig].
 *
 * Created by csicar on 11.01.17.
 * @author Carsten Csiky
 */
class ConfigDialogPane : DialogPane() {
    val nuxmvFilename: FileSelectionField = FileSelectionField()
    val z3Path: FileSelectionField = FileSelectionField()
    val maxLineRollout: PositiveIntegerInputField = PositiveIntegerInputField()
    val verificationTimeout: PositiveIntegerInputField = PositiveIntegerInputField()
    val simulationTimeout: PositiveIntegerInputField = PositiveIntegerInputField()
    val editorFontSize: PositiveIntegerInputField = PositiveIntegerInputField()
    val editorFontFamily: TextField = TextField()
    val okButtonType: ButtonType = ButtonType("Save", ButtonBar.ButtonData.OK_DONE)

    /**
     * Creates the view for a config dialog.
     *
     * Text fields and checkboxes have to be initialized from a
     * [edu.kit.iti.formal.stvs.model.config.GlobalConfig] model. For that, use the
     * [ConfigDialogManager].
     *
     */
    init {
        this.buttonTypes.addAll(okButtonType, ButtonType.CANCEL)

        val grid = GridPane()
        grid.hgap = 10.0
        grid.vgap = 10.0
        grid.padding = Insets(20.0, 10.0, 10.0, 10.0)

        grid.add(Label("Verification Timeout"), 0, 0)
        grid.add(verificationTimeout, 1, 0)

        grid.add(Label("Simulation Timeout"), 0, 1)
        grid.add(simulationTimeout, 1, 1)

        grid.add(Label("Editor Fontsize"), 0, 2)
        grid.add(editorFontSize, 1, 2)

        grid.add(Label("Editor Font Family"), 0, 3)
        grid.add(editorFontFamily, 1, 3)

        grid.add(Label("Path to NuXmv Executable"), 0, 6)
        grid.add(nuxmvFilename, 1, 6)

        grid.add(Label("Path to Z3"), 0, 7)
        grid.add(z3Path, 1, 7)

        grid.add(Label("Maximum Number of Rollouts per Line"), 0, 11)
        grid.add(maxLineRollout, 1, 11)
        this.content = grid
        ViewUtils.setupClass(this)
    }
}
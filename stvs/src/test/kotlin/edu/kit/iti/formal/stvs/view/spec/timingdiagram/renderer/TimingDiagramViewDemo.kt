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
package edu.kit.iti.formal.stvs.view.spec.timingdiagram.renderer

import edu.kit.iti.formal.stvs.view.JavaFxTest
import javafx.scene.Scene
import org.junit.Ignore
import org.junit.jupiter.api.Tag
import org.junit.jupiter.api.Test
import java.util.function.Supplier

/**
 * Created by leonk on 02.02.2017.
 */
@Tag("demo")
class TimingDiagramViewDemo {
    @Ignore
    @Test
    fun javaFxTest() {
        JavaFxTest.Companion.runView(Supplier<Scene?> { this.simpleScene() })
    }

    private fun simpleScene(): Scene? {
        /*TimingDiagramController controller = new TimingDiagramController(new NumberAxis(),new NumberAxis());
    Pane pane = new Pane();
    pane.getChildren().add(controller.getView());
    Scene scene = new Scene(pane, 800, 600);
    //scene.getStylesheets().add(this.getClass().getResource("style.css").toExternalForm());
    return scene;*/
        return null
    }
}
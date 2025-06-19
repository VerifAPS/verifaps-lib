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

import edu.kit.iti.formal.stvs.StvsApplication
import edu.kit.iti.formal.stvs.StvsVersion.buildId
import edu.kit.iti.formal.stvs.StvsVersion.version
import edu.kit.iti.formal.stvs.view.common.ActualHyperLink
import javafx.geometry.Insets
import javafx.geometry.Pos
import javafx.scene.control.*
import javafx.scene.image.Image
import javafx.scene.image.ImageView
import javafx.scene.layout.HBox
import javafx.scene.layout.VBox
import javafx.scene.text.Font

/**
 * The Dialog Pane that shows 'About' information.
 * Is created when the user clicks on 'Help' -> 'About' and shows the name and version information,
 * etc.
 *
 * Created by csicar on 16.02.17.
 *
 *
 * @author Carsten Csiky
 */
class AboutDialogPane : DialogPane() {
    /**
     * Creates the Dialog Pane that displays 'About' information.
     */
    init {
        val tabPane = TabPane(createAboutTab(), createAcknowledgementsTab())

        tabPane.padding = Insets.EMPTY

        this.content = tabPane
        this.buttonTypes.addAll(ButtonType.CLOSE)
        this.content = tabPane
    }

    companion object {
        private fun createLibrary(name: String, url: String, license: String, licenseUrl: String): HBox {
            val nameView: Hyperlink = ActualHyperLink(name, url)
            val licenseView: Hyperlink = ActualHyperLink(license, licenseUrl)

            val hBox = HBox(nameView, Label("License: "), licenseView)
            hBox.alignment = Pos.CENTER_LEFT
            return hBox
        }

        private fun createAcknowledgementsTab(): Tab {
            val libraries = VBox(
                createLibrary(
                    "iec61131lang",
                    "https://github.com/VerifAPS/iec61131lang",
                    "GPLv3",
                    "https://www.gnu.org/licenses/gpl-3.0.en.html",
                ),

                createLibrary(
                    "Apache Commons Collections",
                    "https://commons.apache.org/proper/commons-collections/",
                    "Apache License Version 2.0",
                    "https://www.apache.org/licenses/LICENSE-2.0",
                ),

                createLibrary(
                    "jsexp",
                    "https://github.com/julianmendez/jsexp",
                    "LGPLv3",
                    "https://www.gnu.org/licenses/lgpl-3.0.txt",
                ),

                createLibrary(
                    "Apache Commons Lang",
                    "https://commons.apache.org/proper/commons-lang/",
                    "Apache License Version 2.0",
                    "https://www.apache.org/licenses/LICENSE-2.0",
                ),

                createLibrary(
                    "Apache Commons IO",
                    "https://commons.apache.org/proper/commons-io/",
                    "Apache License Version 2.0",
                    "https://www.apache.org/licenses/LICENSE-2.0",
                ),

                createLibrary(
                    "gson",
                    "https://github.com/google/gson",
                    "Apache License Version 2.0",
                    "https://github.com/google/gson/blob/master/LICENSE",
                ),

                createLibrary(
                    "richtextfx",
                    "https://github.com/TomasMikula/RichTextFX",
                    "BSD 2-Clause License and GPLv2 with the Classpath Exception",
                    "https://github.com/TomasMikula/RichTextFX/blob/master/LICENSE",
                ),

                createLibrary(
                    "antlr",
                    "http://www.antlr.org/",
                    "BSD 3-Clause License",
                    "https://github.com/antlr/antlr4/blob/master/LICENSE.txt",
                ),

                createLibrary(
                    "JAXB",
                    "https://jaxb.java.net/",
                    "CDDLv1.1 and GPLv2",
                    "https://glassfish.java.net/public/CDDL+GPL_1_1.html",
                ),
            )

            val tab = Tab("Acknowledgements", libraries)
            tab.isClosable = false
            return tab
        }

        private fun createAboutTab(): Tab {
            val logo = Image(StvsApplication::class.java.getResourceAsStream("logo.png"))
            val logoView = ImageView(logo)
            val name = Label("Structured Text Verification Studio")
            name.font = Font.font("DejaVu Sans Mono", 30.0)
            val version = Label(
                "Version: " + version + " built from " +
                    buildId,
            )

            val license: Hyperlink = ActualHyperLink(
                "License: GPLv3",
                "https://github.com/VerifAPS/stvs/blob/master/LICENSE",
            )

            val homepage: Hyperlink = ActualHyperLink(
                "Homepage",
                "http://formal.iti.kit.edu/stvs",
            )

            val repo: Hyperlink = ActualHyperLink(
                "Repository",
                "https://github.com/verifaps/stvs",
            )

            val versionAndLicense = HBox(version, license)
            versionAndLicense.alignment = Pos.CENTER

            val links = HBox(homepage, repo)
            links.alignment = Pos.CENTER

            val aboutBox = VBox(
                logoView,
                name,
                versionAndLicense,
                links,
            )
            aboutBox.alignment = Pos.CENTER
            aboutBox.padding = Insets(20.0, 15.0, 20.0, 15.0)
            val tab = Tab("About", aboutBox)
            tab.isClosable = false
            return tab
        }
    }
}
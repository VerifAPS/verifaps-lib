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
package edu.kit.iti.formal.automation.fbd

import org.jdom2.Element

/**
 * Stuff around parsing ladder diagrams.
 * @author Alexander Weigl
 * @version 1 (30.11.24)
 */
abstract class LDObject(element: Element) {
    val globalId: ULong = element.getAttributeValue("globalId").toULong()
    val height: Int? = element.getAttributeValue("height")?.toInt()
    val width: Int? = element.getAttributeValue("width")?.toInt()
    val executionOrderId: ULong? = element.getAttributeValue("width")?.toULong()
}

/**
 * Describes a graphical object representing a left powerrail
 */
class LeftPowerRail(element: Element) : LDObject(element) {
    val connectionPointOuts = element.getChildren("connectionPointOut").map { ConnectionPointOut(it) }
}

/** Defines a connection point on the consumer side */
class ConnectionPointOut(val element: Element) {
    val globalId: Int? = element.getAttributeValue("globalId")?.toInt()

    /** Relative position of the connection pin. Origin is the anchor position of the
     block.*/
    val relPosition: Position = Position(element.getChild("relPosition"))

    /**
     * The operand is a valid iec variable e.g. avar[0] or an iec expression or
     * multiple token text e.g. a + b (*sum*). An iec 61131-3 parser has to be used to extract
     * variable information.
     */
    val expression: String = element.getChild("expression").textNormalize
}

/**
 * Describes a connection between the consumer entry (eg. input variable of a function
 *  block) and the producer entry (eg. output variable of a function block). It may contain a list of
 * positions that describes the path of the connection.
 */
class Connection(val element: Element) {
    /** All positions of the directed connection path. If any positions are given, the
     list has to contain the first (input pin of the consumer entry) as well as the last (output
     pin of the producer entry).
     */
    val relPosition: Position = Position(element.getChild("relPosition"))

    val globalId = element.getAttributeValue("globalId")?.toInt()

    /**Identifies the entry the connection starts from.*/
    val refLocalId = element.getAttributeValue("refLocalId")?.toULong()

    /**
     * If present: This attribute denotes the name of the VAR_OUTPUT / VAR_IN_OUTparameter of the pou block that is the
     * start of the connection.
     * If not present: If the refLocalId attribute refers to a pou block, the start of the connection is the first output
     * of this block, which is not ENO.
     * If the refLocalId attribute refers to any other entry type, the start of the connection is the
     * elements single native output.
     */
    val formalParameter: String? = element.getAttributeValue("formalParameter")
}

class ConnectionPointIn(val element: Element) {
    /** Relative position of the connection pin. Origin is the anchor position of the
     block.*/
    val relPosition: Position = Position(element.getChild("relPosition"))

    /**
     * The operand is a valid iec variable e.g. avar[0] or an iec expression or
     * multiple token text e.g. a + b (*sum*). An iec 61131-3 parser has to be used to extract
     * variable information.
     */
    val expression: String = element.getChild("expression").textNormalize

    val connection: List<Connection> = element.getChildren("connection").map { Connection(it) }
}
class Position(val element: Element)

/**
 * Describes a graphical object representing a right powerrail
 */
data class RightPowerRail(val element: Element) {
    val position: Position = Position(element.getChild("position"))
    val connectionPointIns = element.getChildren("connectionPointIn").map { ConnectionPointIn(it) }
}

abstract class ThingsOnARail(element: Element) : LDObject(element) {
    /**
     * The operand is a valid boolean iec variable e.g. avar[0]
     */
    val variable: String = element.getAttributeValue("variable")
    val connectionPointIns = element.getChildren("connectionPointIn").map { ConnectionPointIn(it) }
    val connectionPointOuts = element.getChildren("connectionPointOut").map { ConnectionPointOut(it) }

    val negated: Boolean = element.getAttributeValue("negated") == "true"
    val edge: EdgeModifierType =
        element.getAttributeValue("edge")?.let { EdgeModifierType.valueOf(it) } ?: EdgeModifierType.None
    val storage: StorageModifierType =
        element.getAttributeValue("storage")?.let { StorageModifierType.valueOf(it) } ?: StorageModifierType.None
}

/**
 * Describes a graphical object representing a boolean variable which can be
 * used as l-value and r-value at the same time
 */
class Coil(element: Element) : ThingsOnARail(element)

/**
 * Describes a graphical object representing a boolean variable which can be
 * used as l-value and r-value at the same time
 */
class Contact(element: Element) : ThingsOnARail(element)

/**Defines the edge detection behaviour of a variable*/
enum class EdgeModifierType { None, Falling, Rising }

/** Defines the storage mode (S/R) behaviour of a variable */
enum class StorageModifierType { None, Set, Reset }

package edu.kit.iti.formal.automation.datatypes

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
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
 * #L%
 */

import edu.kit.iti.formal.automation.datatypes.values.DateAndTimeData
import edu.kit.iti.formal.automation.datatypes.values.DateData
import edu.kit.iti.formal.automation.datatypes.values.TimeofDayData

/**
 *
 * Abstract AnyDate class.
 *
 * @author weigl
 * @version $Id: $Id
 */
abstract class AnyDate(name: String = "ANY_DATE") : AnyDt(name) {
    object DATE : AnyDate("DATE") {
        override fun repr(obj: Any): String {
            val dt = obj as DateData
            return String.format("DATE#%4d-%2d-%2d",
                    dt.year, dt.month, dt.day)
        }

        override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
            return visitor.visit(this)
        }
    }

    object TIME_OF_DAY : AnyDate("TIME_OF_DAY") {
        override fun repr(obj: Any): String {
            val dt = obj as TimeofDayData
            return String.format("TOD#%2d:%2d:%2d.%3d",
                    dt.hours, dt.minutes, dt.seconds, dt.millieseconds)
        }

        override fun <T> accept(visitor: DataTypeVisitorNN<T>): T {
            return visitor.visit(this)
        }
    }

    object DATE_AND_TIME : AnyDate("DATE_AND_TIME") {
        override fun repr(obj: Any): String {
            val dt = obj as DateAndTimeData
            return String.format("DT#%4d-%2d-%2d-%2d:%2d:%2d.%3d",
                    dt.year, dt.month, dt.day, dt.hours, dt.minutes, dt.seconds, dt.millieSeconds)
        }


        override fun <T> accept(visitor: DataTypeVisitorNN<T>) = visitor.visit(this)
    }
}

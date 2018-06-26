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
package edu.kit.iti.formal.automation.testtables.io


import edu.kit.iti.formal.automation.testtables.schema.DataType
import edu.kit.iti.formal.smv.SMVType
import edu.kit.iti.formal.smv.SMVTypes
import edu.kit.iti.formal.smv.SMVWordType

import java.util.HashMap
import java.util.function.Function

/**
 * Created by weigl on 11.12.16.
 */
class DataTypeTranslator : Function<DataType, SMVType?> {
    private val map = HashMap<DataType, SMVType>()

    init {
        map[DataType.INT] = SMVWordType(true, 16)
        map[DataType.LINT] = SMVWordType(true, 64)
        map[DataType.SINT] = SMVWordType(true, 8)
        map[DataType.DINT] = SMVWordType(true, 32)

        map[DataType.UINT] = SMVWordType(false, 16)
        map[DataType.ULINT] = SMVWordType(false, 64)
        map[DataType.USINT] = SMVWordType(false, 8)
        map[DataType.UDINT] = SMVWordType(false, 32)


        map[DataType.WORD] = SMVWordType(false, 16)
        map[DataType.DWORD] = SMVWordType(false, 32)
        map[DataType.LWORD] = SMVWordType(false, 64)
        map[DataType.BYTE] = SMVWordType(false, 8)


        map[DataType.BOOLEAN] = SMVTypes.BOOLEAN
    }

    override fun apply(dataType: DataType): SMVType? {
        return map[dataType]
    }

    companion object {
        var INSTANCE = DataTypeTranslator()
    }
}

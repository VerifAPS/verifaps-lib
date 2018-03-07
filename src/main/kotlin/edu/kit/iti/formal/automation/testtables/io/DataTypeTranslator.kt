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
import edu.kit.iti.formal.smv.ast.GroundDataType
import edu.kit.iti.formal.smv.ast.SMVType

import java.util.HashMap
import java.util.function.Function

/**
 * Created by weigl on 11.12.16.
 */
class DataTypeTranslator : Function<DataType, SMVType?> {
    private val map = HashMap<DataType, SMVType>()

    init {
        map[DataType.INT] = SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 16)
        map[DataType.LINT] = SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 64)
        map[DataType.SINT] = SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 8)
        map[DataType.DINT] = SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 32)

        map[DataType.UINT] = SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 16)
        map[DataType.ULINT] = SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 64)
        map[DataType.USINT] = SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 8)
        map[DataType.UDINT] = SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 32)


        map[DataType.WORD] = SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 16)
        map[DataType.DWORD] = SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 32)
        map[DataType.LWORD] = SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 64)
        map[DataType.BYTE] = SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 8)


        map[DataType.BOOLEAN] = SMVType.BOOLEAN
    }

    override fun apply(dataType: DataType): SMVType? {
        return map[dataType]
    }

    companion object {
        var INSTANCE = DataTypeTranslator()
    }
}

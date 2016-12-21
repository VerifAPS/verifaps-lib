package edu.kit.iti.formal.automation.testtables.io;

/*-
 * #%L
 * geteta
 * %%
 * Copyright (C) 2016 Alexander Weigl
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

import edu.kit.iti.formal.automation.testtables.schema.DataType;
import edu.kit.iti.formal.smv.ast.GroundDataType;
import edu.kit.iti.formal.smv.ast.SMVType;

import java.util.HashMap;
import java.util.function.Function;

/**
 * Created by weigl on 11.12.16.
 */
public class DataTypeTranslator implements Function<DataType, SMVType> {
    public static DataTypeTranslator INSTANCE = new DataTypeTranslator();
    private HashMap<DataType, SMVType> map = new HashMap<>();

    public DataTypeTranslator() {
        map.put(DataType.INT, new SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 16));
        map.put(DataType.LINT, new SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 64));
        map.put(DataType.SINT, new SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 8));
        map.put(DataType.DINT, new SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, 32));

        map.put(DataType.UINT, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 16));
        map.put(DataType.ULINT, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 64));
        map.put(DataType.USINT, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 8));
        map.put(DataType.UDINT, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 32));


        map.put(DataType.WORD, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 16));
        map.put(DataType.DWORD, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 32));
        map.put(DataType.LWORD, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 64));
        map.put(DataType.BYTE, new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, 8));


        map.put(DataType.BOOLEAN, SMVType.BOOLEAN);
    }

    @Override
    public SMVType apply(DataType dataType) {
        return map.get(dataType);
    }
}

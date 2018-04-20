package edu.kit.iti.formal.automation.smv.translators;

/*-
 * #%L
 * iec-symbex
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

import edu.kit.iti.formal.automation.datatypes.AnyDt;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.smv.SMVType;
import edu.kit.iti.formal.smv.ast.SVariable;
import lombok.Getter;

import java.util.HashMap;
import java.util.Map;

/**
 * @author Alexander Weigl
 */
public class TableDataTypeTranslator implements TypeTranslator {
    /**
     */
    private Map<AnyDt, SMVType> map = new HashMap<>();

    /**
     *
     */
    @Getter
    private Map<String, Integer> integerMap = new HashMap<>();

    private DefaultTypeTranslator dttFallback = new DefaultTypeTranslator();

    /**
     *
     *
     */
    @Override
    public SMVType translate(AnyDt datatype) {
        return map.computeIfAbsent(datatype, dttFallback::translate);
    }

    /**
     * {@inheritDoc}
     *
     * @param vdecl
     * @return
     */
    @Override
    public SVariable translate(VariableDeclaration vdecl) {
        if (integerMap.containsKey(vdecl.getName())) {
            int i = integerMap.get(vdecl.getName());
            if (i == 0)
                return SVariable.Companion.create(vdecl.getName()).asBool();
            return SVariable.Companion.create(vdecl.getName())
                    .with(i, i < 0);
        } else {
            return SVariable.Companion.create(vdecl.getName()).with(translate(vdecl.getDataType()));
        }
    }
}

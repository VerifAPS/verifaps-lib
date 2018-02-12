/*
 * #%L
 * iec61131lang
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

package edu.kit.iti.formal.automation.stoo.trans;

import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.stoo.STOOSimplifier;

import java.util.ArrayList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Transform class into records. Remove interfaces.
 *
 * @author Augusto Modanese
 */
public class ClassToRecord extends STOOTransformation {
    @Override
    public void transform(STOOSimplifier.State state) {
        super.transform(state);
        TypeDeclarations records = new TypeDeclarations();
        for (TopLevelElement tle : new ArrayList<>(state.getTopLevelElements())) {
            if (tle instanceof InterfaceDeclaration)
                state.getTopLevelElements().remove(tle);
            else if (tle instanceof ClassDeclaration) {
                state.getTopLevelElements().remove(tle);
                // Struct should only contain internal state variables
                List<VariableDeclaration> fields = ((ClassDeclaration) tle).getScope().stream()
                        .filter(v -> !v.isInput() && !v.isOutput() && !v.isInOut())
                        .collect(Collectors.toList());
                records.add(new StructureTypeDeclaration(((ClassDeclaration) tle).getName(), fields));
            }
        }
        state.getTopLevelElements().add(records);
    }
}

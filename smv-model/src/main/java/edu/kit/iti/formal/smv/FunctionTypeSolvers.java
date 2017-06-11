package edu.kit.iti.formal.smv;

/*-
 * #%L
 * smv-model
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

import edu.kit.iti.formal.smv.ast.GroundDataType;
import edu.kit.iti.formal.smv.ast.SFunction;
import edu.kit.iti.formal.smv.ast.SMVType;
import jdk.nashorn.internal.ir.FunctionCall;

/**
 * @author Alexander Weigl
 * @version 1 (12.12.16)
 */
public class FunctionTypeSolvers {
    public static final FunctionTypeSolver FIRST_ARGUMENT =
            (SFunction f) -> f.getArguments().get(0).getSMVType();

    public static final FunctionTypeSolver LAST_ARGUMENT =
            (SFunction f) -> f.getArguments().get(f.getArguments().size() - 1).getSMVType();

    public static final FunctionTypeSolver TO_SIGNED =
            (SFunction f) -> {
                SMVType.SMVTypeWithWidth dt = (SMVType.SMVTypeWithWidth) FIRST_ARGUMENT.getDataType(f);
                return new SMVType.SMVTypeWithWidth(GroundDataType.SIGNED_WORD, dt.getWidth());
            };

    public static final FunctionTypeSolver TO_UNSIGNED =
            (SFunction f) -> {
                SMVType.SMVTypeWithWidth dt = (SMVType.SMVTypeWithWidth) FIRST_ARGUMENT.getDataType(f);
                return new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, dt.getWidth());
            };

    static class SpecificType implements FunctionTypeSolver {
        private SMVType dt;

        public SpecificType(SMVType dt) {
            this.dt = dt;
        }

        @Override
        public SMVType getDataType(SFunction f) {
            return dt;
        }
    }


}

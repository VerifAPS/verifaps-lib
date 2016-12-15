package edu.kit.iti.formal.smv;

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
            (SFunction f) -> f.getArguments()[0].getSMVType();

    public static final FunctionTypeSolver LAST_ARGUMENT =
            (SFunction f) -> f.getArguments()[f.getArguments().length - 1].getSMVType();

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

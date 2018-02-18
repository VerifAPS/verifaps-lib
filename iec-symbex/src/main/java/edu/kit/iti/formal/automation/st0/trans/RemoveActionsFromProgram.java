package edu.kit.iti.formal.automation.st0.trans;

import edu.kit.iti.formal.automation.st0.STSimplifier;

/**
 * @author Alexander Weigl
 * @version 1 (18.02.18)
 */
public class RemoveActionsFromProgram implements ST0Transformation{
    @Override
    public void transform(STSimplifier.State state) {
        state.theProgram.getActions().clear();
    }
}

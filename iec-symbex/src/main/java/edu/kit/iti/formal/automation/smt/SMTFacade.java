package edu.kit.iti.formal.automation.smt;

import edu.kit.iti.formal.smv.ast.SMVModule;

import javax.annotation.Nonnull;

/**
 * @author Alexander Weigl
 * @version 1 (15.10.17)
 */
public class SMTFacade {
    /**
     *
     * @param module
     * @return
     * @see edu.kit.iti.formal.automation.SymbExFacade
     */
    public static SMTProgram translate(@Nonnull SMVModule module) {
        SSA2SMT s2s = new SSA2SMT(module);
        s2s.run();
        return s2s.getProduct();
    }
}

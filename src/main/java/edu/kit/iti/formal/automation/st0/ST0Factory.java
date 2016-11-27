package edu.kit.iti.formal.automation.st0;

import edu.kit.iti.formal.automation.st.ast.TopLevelElements;

/**
 * @author weigla
 * @date 04.07.2014
 */
public class ST0Factory {

    public static TopLevelElements simplify(TopLevelElements blocks) {
        STSimplifier stSimplifier = new STSimplifier(blocks);
        stSimplifier.transform();
        blocks = stSimplifier.getProcessed();
        return blocks;
    }
}

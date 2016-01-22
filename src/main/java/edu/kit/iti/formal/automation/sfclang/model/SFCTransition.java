package edu.kit.iti.formal.automation.sfclang.model;

import edu.kit.iti.formal.automation.ast.Expression;

import java.util.Set;

/**
 * Created by weigl on 22.01.16.
 */
public class SFCTransition {
    public Set<SFCStep> from, to;
    public Expression guard;
}

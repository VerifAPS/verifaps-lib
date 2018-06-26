package edu.kit.iti.formal.automation.plcopenxml.sfc;

/*-
 * #%L
 * jpox
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.plcopenxml.model.SFCAction;
import edu.kit.iti.formal.automation.plcopenxml.model.SFCGraph;
import edu.kit.iti.formal.automation.plcopenxml.scheme.Body;

import java.util.List;
import java.util.Map;

/**
 * @author weigla
 * @date 26.06.2014
 */
public class JumpStepBuilder extends SFCBuilder {
    private final Body.SFC.JumpStep jump;
    private StepBuilder jumpToBuilder;

    public JumpStepBuilder(Body.SFC.JumpStep step) {
        this.jump = step;
    }

    @Override
    public void connect(Map<Integer, SFCBuilder> nodes, Map<String, SFCAction> actions) {
        registerConnections(nodes, jump.getConnectionPointIn().getConnection());
        for (SFCBuilder b : nodes.values()) {
            if (b instanceof StepBuilder) {
                StepBuilder sb = (StepBuilder) b;
                if (jump.getTargetName().equals(sb.node.name)) {
                    this.jumpToBuilder = sb;
                }
            }
        }
    }

    @Override
    public void canonical() {

    }

    @Override
    public boolean builtNode() {
        return true;
    }

    @Override
    public SFCGraph.Step getProduct() {
        return jumpToBuilder.getProduct();
    }

    @Override
    public List<SFCGraph.Transition> getTransitions() {
        try {
            return jumpToBuilder.getTransitions();
        } catch (NullPointerException e) {
            throw new IllegalStateException("Could not find a step with name " + jump.getTargetName(), e);
        }
    }
}

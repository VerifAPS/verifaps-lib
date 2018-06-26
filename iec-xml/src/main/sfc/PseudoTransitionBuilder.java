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
import edu.kit.iti.formal.automation.datatypes.AnyBit;
import edu.kit.iti.formal.automation.datatypes.values.ScalarValue;
import edu.kit.iti.formal.automation.plcopenxml.model.SFCGraph;

import java.util.Map;

/**
 * Created by weigl on 07/07/14.
 */
public class PseudoTransitionBuilder extends TransitionBuilder {
    public PseudoTransitionBuilder(SFCGraph.Node from, SFCGraph.Node to) {
        super(null);

        product.conditions.add(new ScalarValue<>(AnyBit.BOOL, true));
        product.from = from;
        product.to = to;
        product.from.outgoing.add(product);
        product.to.incoming.add(product);
    }

    @Override
    public void connect(Map<Integer, SFCBuilder> nodes, Map<String, SFCAction> actions) {
    }

    @Override
    public void canonical() {
    }
}

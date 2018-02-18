package edu.kit.iti.formal.automation.sfclang.ast;

/*-
 * #%L
 * iec61131lang
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

import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.Top;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;

import java.util.ArrayList;
import java.util.List;

/**
 * Top-Level Declaration for a Sequential Function Chart,
 * containing steps, actions, transitions, variables declaration.
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
public class SFCImplementation extends Top<IEC61131Parser.SfcContext> {
    private List<SFCNetwork> networks = new ArrayList<>();
    private List<ActionDeclaration> actions = new ArrayList<>();


    public ActionDeclaration getAction(String name) {
        return actions.stream().filter(
                (ActionDeclaration a) -> a.getName().equals(name)).findFirst().orElse(null);
    }

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public SFCImplementation copy() {
        SFCImplementation sfc = new SFCImplementation();
        networks.forEach(a -> sfc.networks.add(a.copy()));
        throw new IllegalStateException("not implemented yet!");
    }
}

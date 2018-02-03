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
import edu.kit.iti.formal.automation.st.ast.Expression;
import edu.kit.iti.formal.automation.st.ast.Top;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;

import java.util.Set;

/**
 * Created by weigl on 22.01.16.
 *
 * @author weigl
 */
@Data
public class SFCTransition extends Top<IEC61131Parser.TransitionContext> {
    private Set<SFCStep> from, to;
    private Expression guard;
    private String name;
    private int priority;

    @Override
    public Top copy() {
        SFCTransition t = new SFCTransition();
        t.setName(name);
        t.setFrom(from); //TODO deep copy
        t.setTo(to); // TODO deep copy
        return t;
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}

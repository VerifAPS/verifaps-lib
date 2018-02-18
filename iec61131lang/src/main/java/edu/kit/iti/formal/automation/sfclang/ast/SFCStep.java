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
import java.util.stream.Collectors;

/**
 * Created by weigl on 22.01.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
public class SFCStep extends Top<IEC61131Parser.StepContext> {
    private String name;
    private boolean isInitial;
    private List<AssociatedAction> events = new ArrayList<>();
    private List<SFCTransition> outgoing = new ArrayList<>(), incoming = new ArrayList<>();

    public AssociatedAction addAction(SFCActionQualifier qualifier, String text) {
        AssociatedAction aa = new AssociatedAction();
        aa.setActionName(text);
        aa.setQualifier(qualifier);
        events.add(aa);
        return aa;
    }

    @Override
    public SFCStep copy() {
        SFCStep s = new SFCStep();
        s.setName(getName());
        s.setInitial(isInitial);
        s.events = events.stream().map(e -> e.copy()).collect(Collectors.toList());
        s.outgoing = new ArrayList<>(outgoing);
        s.incoming = new ArrayList<>(incoming);
        return s;
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Data
    public class AssociatedAction {
        private SFCActionQualifier qualifier;
        private String actionName;

        public AssociatedAction copy() {
            AssociatedAction aa = new AssociatedAction();
            aa.setActionName(actionName);
            aa.setQualifier(qualifier.copy());
            return aa;
        }
    }
}

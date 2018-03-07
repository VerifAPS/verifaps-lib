package edu.kit.iti.formal.automation.st.ast;

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

import edu.kit.iti.formal.automation.datatypes.AnyDt;
import edu.kit.iti.formal.automation.sfclang.ast.ActionDeclaration;
import edu.kit.iti.formal.automation.sfclang.ast.SFCImplementation;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;
import lombok.ToString;

import java.util.LinkedHashMap;
import java.util.Map;


/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
@Data
@EqualsAndHashCode(callSuper = true, exclude = {"stBody", "sfcBody"})
@ToString(callSuper = true)
@NoArgsConstructor
public class FunctionBlockDeclaration extends ClassDeclaration implements Invocable {
    private StatementList stBody;
    private SFCImplementation sfcBody;
    private String name;
    private Map<String, ActionDeclaration> actions = new LinkedHashMap<>();

    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getIdentifier() {
        return getName();
    }

    public AnyDt getReturnType() {
        return null;  // no return value when invoking function blocks
    }

    @Override
    public FunctionBlockDeclaration copy() {
        FunctionBlockDeclaration fb = new FunctionBlockDeclaration();
        fb.setRuleContext(getRuleContext());
        fb.setName(getName());

        if (stBody != null)
            fb.stBody = stBody.copy();
        if (sfcBody != null)
            fb.sfcBody = sfcBody.copy();

        actions.forEach((k, v) -> fb.getActions().put(k, v.copy()));

        fb.setFinal_(isFinal_());
        fb.setAbstract_(isAbstract_());
        fb.setParent(getParent().getIdentifier());
        getInterfaces().forEach(i -> fb.addImplements(i.getIdentifier()));
        getMethods().forEach(m -> fb.getMethods().add(m.copy()));

        return fb;
    }

    public void addAction(ActionDeclaration act) {
        actions.put(act.getName(), act);
    }
}

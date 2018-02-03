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

import edu.kit.iti.formal.automation.sfclang.ast.SFCImplementation;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.EqualsAndHashCode;
import lombok.Getter;
import lombok.Setter;
import lombok.ToString;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
@Getter
@Setter
@EqualsAndHashCode(callSuper = true)
@ToString(callSuper = true)
public class FunctionBlockDeclaration extends ClassDeclaration {
    private StatementList stBody;
    private SFCImplementation sfcBody;
    private String name;

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

    @Override
    public FunctionBlockDeclaration copy() {
        FunctionBlockDeclaration fb = new FunctionBlockDeclaration();
        fb.setRuleContext(getRuleContext());
        fb.setName(getName());
        if (stBody != null)
            fb.stBody = stBody.copy();
        if (sfcBody != null)
            fb.sfcBody = sfcBody.copy();
        return fb;
    }
}

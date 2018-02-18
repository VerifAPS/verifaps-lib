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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.Invocable;
import edu.kit.iti.formal.automation.st.ast.StatementList;
import edu.kit.iti.formal.automation.st.ast.Top;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

/**
 * Created by weigl on 22.01.16.
 *
 * @author weigl
 * @version $Id: $Id
 */
@Data
public class ActionDeclaration extends Top<IEC61131Parser.ActionContext> implements Invocable{
    private @NotNull String name;
    private @Nullable StatementList stBody;
    private @Nullable SFCImplementation sfcBody;

    @Override
    public ActionDeclaration copy() {
        ActionDeclaration a = new ActionDeclaration();
        a.setName(getName());
        if (stBody != null)
            a.stBody = stBody.copy();
        if (sfcBody != null)
            a.sfcBody = sfcBody.copy();
        return a;
    }

    @Override
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public String getIdentifier() {
        return getName();
    }

    @Override
    public Any getReturnType() {
        return null;
    }
}

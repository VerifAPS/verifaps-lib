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
import edu.kit.iti.formal.automation.st.IdentifierPlaceHolder;
import edu.kit.iti.formal.automation.st.LookupList;
import edu.kit.iti.formal.automation.st.LookupListFactory;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.Data;
import lombok.EqualsAndHashCode;
import lombok.NoArgsConstructor;
import lombok.ToString;
import org.antlr.v4.runtime.ParserRuleContext;
import org.jetbrains.annotations.NotNull;
import org.jetbrains.annotations.Nullable;

import java.util.ArrayList;
import java.util.List;


/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl, Augusto Modanese
 * @version $Id: $Id
 */
@Data
@EqualsAndHashCode(callSuper = false)
@ToString(callSuper = true)
@NoArgsConstructor
public final class FunctionBlockDeclaration extends TopLevelScopeElement<ParserRuleContext> implements Invocable {
    @NotNull
    protected final List<IdentifierPlaceHolder<InterfaceDeclaration>> interfaces = new ArrayList<>();

    @NotNull
    protected final List<MethodDeclaration> methods = new ArrayList<>();

    @NotNull
    protected String name = "";

    @NotNull
    private IdentifierPlaceHolder<ClassDeclaration> parent = new IdentifierPlaceHolder<>();

    private boolean final_ = false;
    private boolean abstract_ = false;

    @Nullable
    private StatementList stBody;

    @Nullable
    private SFCImplementation sfcBody;

    private LookupList<ActionDeclaration> actions = LookupListFactory.create();

    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    public AnyDt getReturnType() {
        // TODO replace with DataTypes.VOID?
        return null;  // no return value when invoking function blocks
    }

    @Override
    public String getIdentifier() {
        return getNodeName();
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

        actions.forEach((v) -> fb.getActions().add(v.copy()));

        fb.setFinal_(isFinal_());
        fb.setAbstract_(isAbstract_());
        fb.parent = getParent().copy();
        getInterfaces().forEach(i -> fb.interfaces.add(i.copy()));
        getMethods().forEach(m -> fb.getMethods().add(m.copy()));

        return fb;
    }

    public void addAction(ActionDeclaration act) {
        actions.add(act);
    }

    public void setParentName(String parentName) {
        parent.setIdentifier(parentName);
    }

}



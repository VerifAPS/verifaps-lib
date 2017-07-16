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

import edu.kit.iti.formal.automation.scope.GlobalScope;
import edu.kit.iti.formal.automation.scope.LocalScope;
import org.antlr.v4.runtime.ParserRuleContext;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public abstract class TopLevelScopeElement<T extends ParserRuleContext> extends TopLevelElement<T> {
    protected LocalScope localScope = new LocalScope();

    /**
     * <p>Constructor for TopLevelScopeElement.</p>
     */
    protected TopLevelScopeElement() {

    }

    /**
     * <p>setGlobalScope.</p>
     *
     * @param global a {@link edu.kit.iti.formal.automation.scope.GlobalScope} object.
     */
    public void setGlobalScope(GlobalScope global) {
        localScope.setGlobalScope(global);
    }

    /**
     * <p>Constructor for TopLevelScopeElement.</p>
     *
     * @param p a {@link edu.kit.iti.formal.automation.st.ast.TopLevelScopeElement} object.
     */
    public TopLevelScopeElement(TopLevelScopeElement p) {
        localScope = new LocalScope(p.getLocalScope());
    }

    /**
     * <p>Getter for the field <code>localScope</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.scope.LocalScope} object.
     */
    public LocalScope getLocalScope() {
        return localScope;
    }

    @Override
    public abstract TopLevelScopeElement<T> copy();

    /**
     * <p>Setter for the field <code>localScope</code>.</p>
     *
     * @param localScope a {@link edu.kit.iti.formal.automation.scope.LocalScope} object.
     */
    public void setLocalScope(LocalScope localScope) {
        assert localScope != null;
        this.localScope = localScope;
    }


}

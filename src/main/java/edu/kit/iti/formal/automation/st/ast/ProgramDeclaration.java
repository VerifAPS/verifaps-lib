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

import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class ProgramDeclaration extends TopLevelScopeElement {
    private StatementList programBody;
    private String programName;

    /**
     * <p>Constructor for ProgramDeclaration.</p>
     */
    public ProgramDeclaration() {
    }

    /**
     * <p>Constructor for ProgramDeclaration.</p>
     *
     * @param p a {@link edu.kit.iti.formal.automation.st.ast.ProgramDeclaration} object.
     */
    public ProgramDeclaration(ProgramDeclaration p) {
        super(p);
        programName = p.getProgramName();
        programBody = new StatementList(p.getProgramBody());
    }

    /**
     * <p>Getter for the field <code>programName</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getProgramName() {
        return programName;
    }

    /**
     * <p>Setter for the field <code>programName</code>.</p>
     *
     * @param programName a {@link java.lang.String} object.
     */
    public void setProgramName(String programName) {
        this.programName = programName;
    }

    /**
     * <p>Getter for the field <code>programBody</code>.</p>
     *
     * @return a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public StatementList getProgramBody() {
        return programBody;
    }

    /**
     * <p>Setter for the field <code>programBody</code>.</p>
     *
     * @param programBody a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public void setProgramBody(StatementList programBody) {
        this.programBody = programBody;
    }

    /** {@inheritDoc} */
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override public String getIdentifier() {
        return getProgramName();
    }

    public ProgramDeclaration clone() {
        ProgramDeclaration pd = new ProgramDeclaration();
        pd.programName = programName;
        pd.programBody = programBody.clone();
        return pd;
    }
}

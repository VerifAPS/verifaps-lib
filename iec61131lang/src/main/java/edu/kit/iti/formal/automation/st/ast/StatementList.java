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

import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class StatementList extends ArrayList<Statement> implements Visitable {
    /**
     * <p>Constructor for StatementList.</p>
     */
    public StatementList() {
    }

    /**
     * <p>Constructor for StatementList.</p>
     *
     * @param then a {@link edu.kit.iti.formal.automation.st.ast.Statement} object.
     */
    public StatementList(Statement... then) {
        super(Arrays.asList(then));
    }

    /**
     * <p>Constructor for StatementList.</p>
     *
     * @param statements a {@link edu.kit.iti.formal.automation.st.ast.StatementList} object.
     */
    public StatementList(StatementList statements) {
        addAll(statements);
    }

    public StatementList(List<Statement> ts) {
        super(ts);
    }

    /**
     * {@inheritDoc}
     */
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean add(Statement statement) {
        if (statement == null)
            return false;
        return super.add(statement);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void add(int index, Statement element) {
        if (element == null)
            return;

        super.add(index, element);
    }

    /**
     * <p>comment.</p>
     *
     * @param format a {@link java.lang.String} object.
     * @param args   a {@link java.lang.Object} object.
     */
    public void comment(String format, Object... args) {
        add(new CommentStatement(format, args));
    }

    public StatementList clone() {
        StatementList sl = new StatementList();
        forEach(s -> sl.add(s.clone()));
        return sl;
    }
}

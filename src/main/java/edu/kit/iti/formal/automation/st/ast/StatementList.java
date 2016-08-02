package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.ArrayList;
import java.util.Arrays;

/**
 * Created by weigla on 09.06.2014.
 */
public class StatementList extends ArrayList<Statement> implements Visitable {
    public StatementList() {
    }

    public StatementList(Statement... then) {
        super(Arrays.asList(then));
    }

    public StatementList(StatementList statements) {
        addAll(statements);
    }

    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public boolean add(Statement statement) {
        if (statement == null)
            return false;
        return super.add(statement);
    }

    @Override
    public void add(int index, Statement element) {
        if (element == null)
            return;

        super.add(index, element);
    }

    public void comment(String format, Object... args) {
        add(new CommentStatement(format, args));
    }
}

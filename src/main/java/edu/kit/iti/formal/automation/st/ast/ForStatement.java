package edu.kit.iti.formal.automation.st.ast;


import edu.kit.iti.formal.automation.visitors.Visitor;

/**
 * Created by weigla on 09.06.2014.
 */
public class ForStatement extends Statement {
    private String variable;
    private Expression start, stop, step;
    private StatementList statements = new StatementList();

    public ForStatement() {
    }

    public ForStatement(String variable, Expression start, Expression stop, Expression step, StatementList statements) {
        this.variable = variable;
        this.start = start;
        this.stop = stop;
        this.step = step;
        this.statements = statements;
    }

    public String getVariable() {
        return variable;
    }

    public void setVariable(String variable) {
        this.variable = variable;
    }

    public Expression getStart() {
        return start;
    }

    public void setStart(Expression start) {
        this.start = start;
    }

    public Expression getStop() {
        return stop;
    }

    public void setStop(Expression stop) {
        this.stop = stop;
    }

    public Expression getStep() {
        return step;
    }

    public void setStep(Expression step) {
        this.step = step;
    }

    public StatementList getStatements() {
        return statements;
    }

    public void setStatements(StatementList statements) {
        this.statements = statements;
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}

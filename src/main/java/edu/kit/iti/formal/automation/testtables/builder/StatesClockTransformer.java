package edu.kit.iti.formal.automation.testtables.builder;

/*-
 * #%L
 * geteta
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

/**
 * Created by weigl on 17.12.16.
 *
@Deprecated
public class StatesClockTransformer implements TableTransformer {
    private static final int INITIAL_CLOCK_VALUE = 1;
    private TableModule mt;
    private GeneralizedTestTable gtt;
    private StateReachability reachable;
    private SVariable errorState;

    private void createStates() {
        List<State> flat = gtt.getRegion().flat();
        flat.forEach(this::introduceState);
        flat.forEach(this::addNextAssignments);
        insertErrorState();
        insertInitialState();
    }

    private void introduceState(State s) {
        Duration d = s.getDuration();
        mt.getStateVars().add(s.getSMVVariable());

        SMVExpr clockVariableKeep;
        SMVExpr clockVariableFwd;

        if (d.isOneStep()) { // [1,1]
            clockVariableFwd = SLiteral.TRUE;
            clockVariableKeep = SLiteral.FALSE;
        } else if (d.getLower() == 0 && d.isUnbounded()) {
            clockVariableFwd = SLiteral.TRUE;
            clockVariableKeep = SLiteral.TRUE;
        } else {
            //excluded 1, [0,*]
            //possible [n,m], [0,m], [n,*]
            SVariable clock = introduceClock(s);

            if (d.getLower() <= 0) {
                clockVariableFwd = SLiteral.TRUE;
            } else {
                clockVariableFwd = new SBinaryExpression(clock,
                        SBinaryOperator.GREATER_EQUAL,
                        new SLiteral(clock.getSMVType(), d.getLower()));
            }

            if (d.getUpper() == -1) {
                clockVariableKeep = SLiteral.TRUE;
            } else {
                clockVariableKeep = new SBinaryExpression(clock,
                        SBinaryOperator.LESS_THAN,
                        new SLiteral(clock.getSMVType(), d.getUpper()));
            }
        }

        // define output predicate
        mt.getDefinitions().put(s.getDefOutput(),
                SMVFacade.combine(SBinaryOperator.AND, s.getOutputExpr(), SLiteral.TRUE));

        // define input predicate
        mt.getDefinitions().put(s.getDefInput(),
                SMVFacade.combine(SBinaryOperator.AND, s.getInputExpr(), SLiteral.TRUE));

        // define keep predicate
        mt.getDefinitions().put(s.getDefFailed(),
                SMVFacade.combine(SBinaryOperator.AND,
                        s.getSMVVariable(), s.getDefInput(), s.getDefOutput(), clockVariableKeep));

        // define forward predicate
        mt.getDefinitions().put(s.getDefForward(),
                SMVFacade.combine(SBinaryOperator.AND,
                        s.getSMVVariable(), s.getDefInput(), s.getDefOutput(), clockVariableFwd));
    }

    private SVariable introduceClock(State s) {

        //region Find suitable datatype
        int concreteValue = gtt.getOptions().getConcreteTableOptions().getCount(s.getId(), -1);
        int max = Math.max(concreteValue, s.getDuration().maxCounterValue());
        int bits = (int) Math.ceil(Math.log(1 + max) / Math.log(2));
        SMVType.SMVTypeWithWidth dt = new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, bits);
        //endregion

        // clock variable
        SVariable clockModule = new SVariable("clock" + s.getId(), dt);

        // definitions
        SVariable reset = new SVariable("clock" + s.getId() + "_rs", dt);
        SVariable inc = new SVariable("clock" + s.getId() + "_tic", dt);
        SVariable limit = new SVariable("clock" + s.getId() + "_limit", dt);

        // change to due issues #5
        mt.getDefinitions()
                .put(reset, SMVFacade.next(SMVFacade.NOT(s.getSMVVariable())));
        mt.getDefinitions().put(inc, s.getDefFailed());
        mt.getDefinitions().put(limit, // c > 0dX_MAX
                new SBinaryExpression(clockModule,
                        SBinaryOperator.GREATER_THAN,
                        new SLiteral(dt, max)));

        // clock assignments
        SAssignment init = new SAssignment(clockModule, new SLiteral(dt, INITIAL_CLOCK_VALUE));
        SAssignment next = new SAssignment(clockModule, SMVFacade.caseexpr(
                reset, new SLiteral(dt, 0),
                SMVFacade.combine(SBinaryOperator.AND, inc, limit), clockModule,
                inc, new SBinaryExpression(clockModule, SBinaryOperator.PLUS,
                        new SLiteral(dt, 1)),
                SMVFacade.next(s.getSMVVariable()), new SLiteral(dt, INITIAL_CLOCK_VALUE)
        ));

        mt.getStateVars().add(clockModule);
        mt.getInitAssignments().add(init);
        mt.getNextAssignments().add(next);
        mt.getClocks().put(s, clockModule);
        return clockModule;
    }


    private void addNextAssignments(State inc) {
        // I get actived if one of my outgoing is valid
        SMVExpr or = reachable.getIncoming(inc)
                .map(State::getDefForward)
                .map(fwd -> (SMVExpr) fwd)
                .reduce(SMVFacade.reducer(SBinaryOperator.OR))
                .orElseGet(() -> SLiteral.FALSE);

        SAssignment assignment = new SAssignment(inc.getSMVVariable(),
                SMVFacade.combine(SBinaryOperator.OR,
                        or, inc.getDefFailed()));
        mt.getNextAssignments().add(assignment);
    }

    private void insertErrorState() {
        // new error state
        mt.getStateVars().add(errorState);

        // disable in the beginning
        mt.getInit().add(SMVFacade.NOT(errorState));

        SMVExpr e = reachable.getStates().stream()
                .map(s ->
                        // s_i & I_i & !O_i
                        SMVFacade.combine(SBinaryOperator.AND,
                                s.getSMVVariable(),
                                s.getDefInput(),
                                SMVFacade.NOT(s.getDefOutput())))
                .reduce(SMVFacade.reducer(SBinaryOperator.OR))
                .get();

        SAssignment a = new SAssignment(errorState, e);
        mt.getNextAssignments().add(a);
    }

    public void insertInitialState() {
        reachable.getStates().forEach(s ->
                mt.getInit().add(
                        !reachable.isInitialReachable(s)
                                ? SMVFacade.NOT(s.getSMVVariable())
                                : s.getSMVVariable()));
    }

    @Override
    public void accept(TableTransformation tt) {
        mt = tt.getTableModule();
        gtt = tt.getTestTable();
        reachable = tt.getReachable();
        errorState = tt.getErrorState();
        createStates();
    }
}
*/
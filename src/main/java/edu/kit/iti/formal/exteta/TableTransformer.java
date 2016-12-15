package edu.kit.iti.formal.exteta;

import edu.kit.iti.formal.exteta.io.IOFacade;
import edu.kit.iti.formal.exteta.io.Report;
import edu.kit.iti.formal.exteta.model.Duration;
import edu.kit.iti.formal.exteta.model.GeneralizedTestTable;
import edu.kit.iti.formal.exteta.model.State;
import edu.kit.iti.formal.exteta.model.TableModule;
import edu.kit.iti.formal.exteta.schema.ConstraintVariable;
import edu.kit.iti.formal.smv.SMVFacade;
import edu.kit.iti.formal.smv.ast.*;

public class TableTransformer {
    private final StateReachability reachability;
    private GeneralizedTestTable gtt;
    private TableModule mt = new TableModule();
    private SVariable errorState = new SVariable("ERROR", SMVType.BOOLEAN);

//    private List<Transformation> transformations = new LinkedList<>();

    public TableTransformer(GeneralizedTestTable table) {
        this.gtt = table;
        reachability = new StateReachability(table);
    }

    public SMVModule transform() {
        transformName();
        moduleParameters();
        addConstraintVariables();
        createStates();
        addInvarSpec();

        return mt;
    }

    private void transformName() {
        if (mt.getName() == null || mt.getName().isEmpty()) {
            Report.fatal("No table name given.");
        }

        mt.setName(gtt.getName());
    }

    private void moduleParameters() {
        for (String cv : gtt.getIoVariables().keySet()) {
            SVariable var = gtt.getSMVVariable(cv);
            mt.getModuleParameter().add(var);
        }
    }

    private void addConstraintVariables() {
        for (ConstraintVariable cv : gtt.getConstraintVariable().values()) {
            SVariable var = gtt.getSMVVariable(cv.getName());
            mt.getFrozenVars().add(var);
            mt.getInit().add(IOFacade.parseCellExpression(cv.getConstraint(), var, gtt));
            //TODO add invar for each frozenvar
        }
    }

    private void createStates() {
        for (State s : gtt.getRegion().getStates()) {
            introduceState(s);
        }

        addInitState();

        for (State s : reachability.getStates()) {
            addState(s);
        }

        errorState();
    }

    private void introduceState(State s) {
        Duration d = s.getDuration();
        mt.getStateVars().add(s.getSMVVariable());

        SMVExpr clockVariableKeep;
        SMVExpr clockVariableFwd;
        if (d.isOneStep()) { // [1,1]
            clockVariableFwd = SLiteral.TRUE;
            clockVariableKeep = SLiteral.FALSE;
        } else if (d.isUnbounded()) {
            clockVariableFwd = SLiteral.TRUE;
            clockVariableKeep = SLiteral.TRUE;
        } else {
            //excluded 1, [0,*]
            //possible [n,m], [0,m], [n,*]
            SVariable clock = introduceClock(s);

            if (d.lower <= 0) {
                clockVariableFwd = SLiteral.TRUE;
            } else {
                clockVariableFwd = new SBinaryExpression(clock,
                        SBinaryOperator.GREATER_EQUAL,
                        new SLiteral(clock.getSMVType(), d.lower));
            }

            if (d.upper == -1) {
                clockVariableKeep = SLiteral.TRUE;
            } else {
                clockVariableKeep = new SBinaryExpression(clock,
                        SBinaryOperator.LESS_THAN,
                        new SLiteral(clock.getSMVType(), d.upper));
            }
        }

        // define output predicate
        mt.getDefinitions().put(s.getDefOutput(),
                SMVFacade.combine(SBinaryOperator.AND, s.getOutputExpr()));

        // define input predicate
        mt.getDefinitions().put(s.getDefInput(),
                SMVFacade.combine(SBinaryOperator.AND, s.getInputExpr()));

        // define input predicate
        mt.getDefinitions().put(s.getDefKeep(),
                SMVFacade.combine(SBinaryOperator.AND,
                        s.getDefInput(), s.getDefOutput(), clockVariableKeep));

        // define input predicate
        mt.getDefinitions().put(s.getDefForward(),
                SMVFacade.combine(SBinaryOperator.AND,
                        s.getDefInput(), s.getDefOutput(), clockVariableFwd));
    }

    private SVariable introduceClock(State s) {
        int max = s.getDuration().maxCounterValue();
        int bits = (int) Math.ceil(Math.log(1 + max)/Math.log(2));
        SMVType.SMVTypeWithWidth dt = new SMVType.SMVTypeWithWidth(GroundDataType.UNSIGNED_WORD, bits);

        // clock variable
        SVariable clockModule = new SVariable("clock" + s.getId(), dt);

        // definitions
        SVariable reset = new SVariable("clock" + s.getId() + "_rs", dt);
        SVariable inc = new SVariable("clock" + s.getId() + "_tic", dt);
        SVariable limit = new SVariable("clock" + s.getId() + "_limit", dt);

        mt.getDefinitions().put(reset, SMVFacade.NOT(s.getDefKeep()));
        mt.getDefinitions().put(inc, s.getDefKeep());
        mt.getDefinitions().put(limit, // c > 0dX_MAX
                new SBinaryExpression(clockModule,
                        SBinaryOperator.GREATER_THAN,
                        new SLiteral(dt, max)));

        // clock assignments
        SAssignment init = new SAssignment(clockModule, new SLiteral(dt, 0));
        SAssignment next = new SAssignment(clockModule, SMVFacade.caseexpr(
                reset, new SLiteral(dt, 0),
                SMVFacade.combine(SBinaryOperator.AND, inc, limit), clockModule,
                inc, new SBinaryExpression(clockModule, SBinaryOperator.PLUS,
                        new SLiteral(dt, 1)),
                SMVFacade.next(s.getSMVVariable()), new SLiteral(dt, 1)
        ));

        mt.getStateVars().add(clockModule);
        mt.getInitAssignments().add(init);
        mt.getNextAssignments().add(next);

        return clockModule;
    }

    private void addState(State inc) {
        // I get actived if one of my outgoing is valid
        SMVExpr or = reachability.getOutgoing(inc)
                .map(State::getDefForward)
                .map(fwd -> (SMVExpr) fwd)
                .reduce(SMVFacade.reducer(SBinaryOperator.OR))
                .orElseGet(() -> SLiteral.FALSE);

        SAssignment assignment = new SAssignment(inc.getSMVVariable(),
                SMVFacade.combine(SBinaryOperator.OR,
                        or, inc.getDefKeep()));
        mt.getNextAssignments().add(assignment);
    }

    private void errorState() {
        // new error state
        mt.getStateVars().add(errorState);

        // disable in the beginning
        mt.getInit().add(SMVFacade.NOT(errorState));

        SMVExpr e = reachability.getStates().stream()
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

    private void addInitState() {
        for (State s : reachability.getStates()) {
            mt.getInit().add(
                    !reachability.isInitialReachable(s)
                            ? SMVFacade.NOT(s.getSMVVariable())
                            : s.getSMVVariable());
        }
    }


    private void addInvarSpec() {
        SMVExpr states = reachability.getStates().stream()
                .map(State::getSMVVariable)
                .map(v -> (SMVExpr) v)
                .reduce(SMVFacade.reducer(SBinaryOperator.OR))
                .get();

        // ! ( \/ states) -> !error
        SMVExpr invar = SMVFacade.combine(SBinaryOperator.IMPL,
                errorState,
                states);

        mt.getInvarSpec().add(invar);
    }
}

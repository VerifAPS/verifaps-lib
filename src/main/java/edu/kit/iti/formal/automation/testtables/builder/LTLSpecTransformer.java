package edu.kit.iti.formal.automation.testtables.builder;

import edu.kit.iti.formal.automation.testtables.model.State;
import edu.kit.iti.formal.smv.SMVFacade;
import edu.kit.iti.formal.smv.ast.SBinaryOperator;
import edu.kit.iti.formal.smv.ast.SLiteral;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.List;
import java.util.stream.Collectors;

/**
 * Construction of the LTL specification for strict conformance.
 * <p>
 * FAIRNESS -> F ( last_states_fwd | non_selected )
 *
 * @author Alexander Weigl
 * @version 1 (03.05.17)
 */
public class LTLSpecTransformer implements TableTransformer {
    @Override public void accept(TableTransformation tt) {
        List<State> steps = tt.getTestTable().getRegion().flat();
        State lastStep = steps.get(steps.size() - 1);
        State.AutomatonState lastAutomataStep = lastStep.getAutomataStates()
                .get(lastStep.getAutomataStates().size() - 1);

        SVariable lastStateForward = lastAutomataStep.getDefForward();

        List<SMVExpr> automataStates = steps.stream()
                .flatMap(s -> s.getAutomataStates().stream())
                .map(as -> as.getSMVVariable().not())
                .collect(Collectors.toList());
        automataStates.add(tt.getErrorState().not());

        SMVExpr noStateSelected = SMVFacade
                .combine(SBinaryOperator.AND, automataStates);

        SMVExpr fairness = steps.stream()
                .flatMap(s -> s.getAutomataStates().stream())
                .filter(State.AutomatonState::isUnbounded)
                .map(State.AutomatonState::getDefForward)
                .map(s -> (SMVExpr) s.eventually().globally())
                .reduce(SMVFacade.reducer(SBinaryOperator.AND))
                .orElse(SLiteral.TRUE);

        SMVExpr ltlspec = fairness
                .implies(noStateSelected.or(lastStateForward).eventually());

        tt.getTableModule().getLTLSpec().add(ltlspec);
    }
}

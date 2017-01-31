package edu.kit.iti.formal.automation.testtables.concretizer;

import com.microsoft.z3.Log;
import edu.kit.iti.formal.automation.testtables.io.IOFacade;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.State;
import edu.kit.iti.formal.automation.testtables.schema.ConstraintVariable;
import edu.kit.iti.formal.automation.testtables.schema.IoVariable;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import org.sosy_lab.common.ShutdownManager;
import org.sosy_lab.common.configuration.Configuration;
import org.sosy_lab.common.configuration.InvalidConfigurationException;
import org.sosy_lab.common.log.BasicLogManager;
import org.sosy_lab.common.log.LogManager;
import org.sosy_lab.java_smt.SolverContextFactory;
import org.sosy_lab.java_smt.api.*;

import java.io.IOException;
import java.util.List;
import java.util.Optional;
import java.util.logging.Level;

import static org.sosy_lab.java_smt.api.SolverContext.ProverOptions;

/**
 * @author Alexander Weigl
 * @version 1 (22.01.17)
 */
public class SMTConcretizer extends DefaultConcretizer {
    private GeneralizedTestTable tt;
    private SolverContext context;
    private BitvectorFormulaManager bitmgr;
    private BooleanFormulaManager boolmgr;
    private SMTVariableFactory vfactory;

    @Override
    public Optional<ConcreteTestTable> apply(GeneralizedTestTable generalizedTestTable) {
        try {
            tt = generalizedTestTable;
            askForDurationInstantiation(tt);
            init();
            try (ProverEnvironment prover =
                         context.newProverEnvironment(ProverOptions.GENERATE_MODELS)) {
                tableIntoSMT(prover);
                callSMT(prover);
                //parseOutput();
            } catch (IOException e) {
                e.printStackTrace();
            } catch (InterruptedException e) {
                e.printStackTrace();
            } catch (SolverException e) {
                e.printStackTrace();
            }
        } catch (InvalidConfigurationException e) {
            e.printStackTrace();
        }
        return Optional.empty();
    }

    private void init() throws InvalidConfigurationException {
        String[] args = new String[]{
                //"--solver.z3.log=z3.log",
                "--solver.useLogger=true",
                "--log.level=INFO"
        };

        Configuration config = Configuration.fromCmdLineArguments(args);
        //System.out.println(config.asPropertiesString());
        //config.dumpUsedOptionsTo(System.out);
        LogManager logger = BasicLogManager.create(config);
        config.enableLogging(logger);
        ShutdownManager shutdown = ShutdownManager.create();
        logger.log(Level.INFO, "test");

        context = SolverContextFactory.createSolverContext(
                config, logger, shutdown.getNotifier(),
                SolverContextFactory.Solvers.Z3);

        vfactory = new SMTVariableFactory(context.getFormulaManager());
        bitmgr = context.getFormulaManager().getBitvectorFormulaManager();
        boolmgr = context.getFormulaManager().getBooleanFormulaManager();
    }

    public void tableIntoSMT(ProverEnvironment prover) {
        prover.addConstraint(boolmgr.makeTrue());


        for (ConstraintVariable var : tt.getConstraintVariable().values()) {
            SMVExpr expr = IOFacade.parseCellExpression(var.getConstraint(),
                    tt.getSMVVariable(var.getName()), tt);
            prover.addConstraint((BooleanFormula) asSMT(expr, 0));
        }

        for (int i = 0; i < cycles.size(); i++) {
            for (IoVariable var : tt.getIoVariables().values()) {
                vfactory.getVariable(var.getName(), var.getDataType(), i);
            }
        }
        prover.push();

        int i = 0;
        for (State state : cycles) {
            Formula in = asSMT(state.getInputExpr(), i);
            prover.addConstraint((BooleanFormula) in);
            Formula o = asSMT(state.getOutputExpr(), i);
            prover.addConstraint((BooleanFormula) o);
            System.out.println(in);
            System.out.println(o);
            i++;
        }
    }

    public void callSMT(ProverEnvironment prover)
            throws IOException, InterruptedException, SolverException {
        boolean isUnsat = prover.isUnsat();
        System.out.println(prover.getModelAssignments());

        if (!isUnsat) {
            Model model = prover.getModel();
            System.out.println(model);
        }
    }

    private Formula asSMT(List<SMVExpr> inputExpr, int i) {
        return inputExpr.stream()
                .map(a -> asSMT(a, i))
                .reduce((a, b) -> boolmgr.and((BooleanFormula) a, (BooleanFormula) b))
                .orElse(boolmgr.makeTrue());

    }

    private Formula asSMT(SMVExpr smvExpr, int i) {
        return smvExpr.accept(new SMTPrinter(context.getFormulaManager(), vfactory, i));
    }
}



package edu.kit.iti.formal.exteta.io;

import java.io.File;
import java.util.List;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.exteta.model.Region;
import edu.kit.iti.formal.exteta.model.State;
import edu.kit.iti.formal.exteta.schema.*;
import edu.kit.iti.formal.smv.ast.SMVExpr;
import edu.kit.iti.formal.exteta.ExTeTa;
import edu.kit.iti.formal.exteta.model.GeneralizedTestTable;

public class TableReader {
    private File input;
    private GeneralizedTestTable gtt = new GeneralizedTestTable();
    private int stepNumber = 0;


    public TableReader(File input) {
        this.input = input;
    }

    public void run() throws JAXBException {
        Report.debug("read xml file %s", input);

        @SuppressWarnings("restriction")
        JAXBContext jc = JAXBContext.newInstance(ObjectFactory.class);
        Unmarshaller jaxbUnmarshaller = jc.createUnmarshaller();
        JAXBElement<?> root = (JAXBElement<?>) jaxbUnmarshaller.unmarshal(input);
        TestTable xml = (TestTable) root.getValue();

        Report.debug("xml file successfully read", input);

        translateName(xml);
        translateOptions(xml);
        translateFunction(xml);
        translateVariables(xml);
        translateSteps(xml);
    }

    private void translateName(TestTable xml) {
        gtt.setName(xml.getName());
    }

    private void translateFunction(TestTable xml) {
        if (xml.getFunctions() == null) {
            Report.info("No functions given in table file.");
            return;
        }

        String func = xml.getFunctions();
        if (!func.isEmpty()) {
            gtt.addFunctions(IEC61131Facade.file(func));
        }
    }

    private void translateOptions(TestTable xml) {
        if (xml.getOptions() == null || xml.getOptions().getOption().isEmpty()) {
            Report.info("No options in table file.");
            return;
        }

        for (Options.Option o : xml.getOptions().getOption()) {
            gtt.addOption(o.getKey(), o.getValue());
        }
    }

    private void translateSteps(TestTable xml) {
        Region r = translateSteps(xml.getSteps().getBlockOrStep());
        gtt.setRegion(r);
    }

    /*for (Step step : xml.getSteps().getBlockOrStep()) {
            stepNumber++;

            if (ExTeTa.DEBUG) {
                System.out.format("Step #%d%n", stepNumber);
            }

            if (step.getCell().size() != xml.getVariables().getVariable().size()) {
                System.err.format("The amount of cells does not match the number of variables in step #%d%n",
                        stepNumber);
            }
                    if (ExTeTa.DEBUG) {
                        System.out.format("\t%s => %s%n", v.getName(), expr);
                    }
                } catch (ParseCancellationException e) {
                    System.err.format("Syntax Error in step %d in cell %d (%s): %s%n", stepNumber, i, cell,
                            e.getMessage());
*/

    private Region translateSteps(List<Object> steps) {
        Region r = new Region(stepNumber++);
        for (Object o : steps) {
            if (o instanceof edu.kit.iti.formal.exteta.schema.Step) {
                Step step = (Step) o;
                r.getStates().add(translateStep(step));
            }

            if (o instanceof Block) {
            /* Block block = (Block) o;
                Region s = translateSteps(block.getStepOrBlock());
                r.setDuration(IOFacade.parseDuration(block.getDuration()));
                r.getStates().add(s);*/
                throw new IllegalStateException("Nested blocks are currently not supported");
            }
        }
        return r;
    }

    private State translateStep(Step step) {
        State s = new State(stepNumber++);

        for (int i = 0; i < step.getCell().size(); i++) {
            IoVariable v = gtt.getIoVariables(i);
            String name = v.getName();
            SMVExpr e = IOFacade.parseCellExpression(step.getCell().get(i),
                    gtt.getSMVVariable(name), gtt);
            s.add(v, e);
        }

        s.setDuration(IOFacade.parseDuration(step.getDuration()));
        return s;
    }

    private void translateVariables(TestTable xml) {
        Report.debug("%d variables found",
                xml.getVariables().getVariableOrConstraint().size());

        for (Object o : xml.getVariables().getVariableOrConstraint()) {
            if (o instanceof IoVariable) {
                IoVariable v = (IoVariable) o;
                Report.debug("\t %s : %s", v.getName(), v.getDataType());
                gtt.add(v);
            }

            if (o instanceof ConstraintVariable) {
                ConstraintVariable v = (ConstraintVariable) o;
                if (ExTeTa.DEBUG)
                    System.out.format("\t %s : %s", v.getName(), v.getDataType());
                gtt.add(v);
            }
        }
    }

    public GeneralizedTestTable getProduct() {
        return gtt;
    }

}

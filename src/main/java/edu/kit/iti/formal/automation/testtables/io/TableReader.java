package edu.kit.iti.formal.automation.testtables.io;

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

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.testtables.model.Duration;
import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.Region;
import edu.kit.iti.formal.automation.testtables.model.State;
import edu.kit.iti.formal.automation.testtables.schema.*;
import edu.kit.iti.formal.smv.ast.SMVExpr;

import javax.xml.bind.JAXBContext;
import javax.xml.bind.JAXBElement;
import javax.xml.bind.JAXBException;
import javax.xml.bind.Unmarshaller;
import java.io.File;
import java.util.List;

public class TableReader {
    private File input;
    private GeneralizedTestTable gtt = new GeneralizedTestTable();
    private int stepNumber = 0;

    public TableReader(File input) {
        this.input = input;
    }

    public void run() throws JAXBException {
        Report.debug("read xml file %s", input);

        @SuppressWarnings("restriction") JAXBContext jc = JAXBContext
                .newInstance(ObjectFactory.class);
        Unmarshaller jaxbUnmarshaller = jc.createUnmarshaller();
        JAXBElement<?> root = (JAXBElement<?>) jaxbUnmarshaller
                .unmarshal(input);
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
        if (xml.getOptions() == null || xml.getOptions().getOption()
                .isEmpty()) {
            Report.info("No options in table file.");
            return;
        }

        for (Options.Option o : xml.getOptions().getOption()) {
            gtt.addOption(o.getKey(), o.getValue());
            Report.info("Option %s set to %s", o.getKey(), o.getValue());
        }
    }

    private void translateSteps(TestTable xml) {
        Region r = translateSteps(xml.getSteps().getBlockOrStep());
        gtt.setRegion(r);
    }

    private Region translateSteps(List<Object> blockOrStep) {
        Block b = new Block();
        b.setDuration("1");
        b.getStepOrBlock().addAll(blockOrStep);
        return translateSteps(b);
    }

    private Region translateSteps(Block steps) {
        Region r = new Region(stepNumber++);
        String duration = steps.getDuration();
        if (duration == null) {
            Report.info("Duration is not given, assume '[1,1]'");
            r.setDuration(new Duration(1, 1));
        }
        else {
            r.setDuration(IOFacade.parseDuration(duration));
        }
        for (Object o : steps.getStepOrBlock()) {
            if (o instanceof Step) {
                r.getStates().add(translateStep((Step) o));
            }
            else if (o instanceof Block) {
                r.getStates().add(translateSteps((Block) o));
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
                Report.debug("\t %s : %s", v.getName(), v.getDataType());
                gtt.add(v);
            }
        }

        gtt.getIoVariables().forEach((k, v) -> {
            if (v.getDataType() == null || v.getName() == null || v.getName()
                    .isEmpty() || v.getIo() == null || v.getIo().isEmpty())
                throw new IllegalArgumentException(
                        "variable " + v.getName() + " is bad");
        });
    }

    public GeneralizedTestTable getProduct() {
        return gtt;
    }

}

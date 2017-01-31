package edu.kit.iti.formal.automation.testtables.concretizer;

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.Region;
import edu.kit.iti.formal.automation.testtables.model.State;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (22.01.17)
 */
public abstract class DefaultConcretizer implements Concretizer {
    protected List<State> cycles = new ArrayList<>(1000);

    protected void askForDurationInstantiation(GeneralizedTestTable tt) {
        askForDurationInstantiation(tt.getRegion());
    }

    private void askForDurationInstantiation(State reg) {
        //console.printf("Please instantiate duration for [%s] with duration: [%s]",
        //        reg.getId(), reg.getDuration());
        //try {
        //    int cycles =  Integer.parseInt(console.readLine());
        //} catch (NumberFormatException e) {
        int cycles = reg.getDuration().getLower();
        //}

        if (reg instanceof Region) {
            List<State> states = ((Region) reg).getStates();
            for (int i = 0; i < cycles; i++)
                states.forEach(this::askForDurationInstantiation);
        } else
            for (int i = 0; i < cycles; i++)
                this.cycles.add(reg);
    }
}

package edu.kit.iti.formal.automation.testtables;

import edu.kit.iti.formal.automation.testtables.model.GeneralizedTestTable;
import edu.kit.iti.formal.automation.testtables.model.Region;
import edu.kit.iti.formal.automation.testtables.model.State;
import edu.kit.iti.formal.automation.testtables.model.TableNode;
import lombok.Getter;
import lombok.RequiredArgsConstructor;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (01.02.18)
 */
@RequiredArgsConstructor
public class OmegaSimplifier implements Runnable {
    private final GeneralizedTestTable gtt;
    @Getter
    private List<State> ignored = new ArrayList<>();

    private boolean abort = false;

    @Override
    public void run() {
        abort = false;
        gtt.setRegion(recur(gtt.getRegion()));
    }

    /**
     * Traverse and copy the tree structure until an \omega appeares as duration, then
     * keep traversing but do not copy. The states are capture to {@link #ignored}
     *
     * @param region
     * @return
     */
    private Region recur(Region region) {
        Region newRegion = new Region(region.getId());
        for (TableNode state : region.getChildren()) {
            if (abort) {
                if (!state.isLeaf()) {
                    recur((Region) state);
                } else {
                    ignored.add((State) state);
                }
            } else {
                if (!state.isLeaf()) {
                    newRegion.getChildren().add(recur((Region) state));
                } else {
                    newRegion.getChildren().add(state);
                }
                if (state.getDuration().isOmega()) {
                    abort = true;
                }
            }
        }
        return newRegion;
    }

    public GeneralizedTestTable getProduct() {
        return gtt;
    }
}

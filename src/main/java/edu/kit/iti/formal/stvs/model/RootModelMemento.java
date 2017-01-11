package edu.kit.iti.formal.stvs.model;

import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;

import java.util.ArrayList;
import java.util.List;

/**
 * Records deep copies of data structures to
 */
public class RootModelMemento {
    private List<HybridSpecification> hybridSpecifications;
    private Code code;

    public RootModelMemento(List<HybridSpecification> hybridSpecifications, Code code) {
        this.hybridSpecifications = new ArrayList<HybridSpecification>();
        for (HybridSpecification spec : hybridSpecifications) {
            this.hybridSpecifications.add(new HybridSpecification(spec));
        }
        this.code = new Code(code);
    }

    public Code getCode() {
        return code;
    }

    public List<HybridSpecification> getHybridSpecifications() {
        return null;
    }
}

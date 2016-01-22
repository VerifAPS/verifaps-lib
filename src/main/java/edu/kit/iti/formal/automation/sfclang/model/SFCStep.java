package edu.kit.iti.formal.automation.sfclang.model;

import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * Created by weigl on 22.01.16.
 */
public class SFCStep {
    public String name;
    public boolean isInitial;
    public Map<String, List<SFCAction>> events = new HashMap<>();
    public List<SFCTransition> outgoing, incoming;
}

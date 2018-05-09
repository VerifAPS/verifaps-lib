package edu.kit.iti.formal.automation.st;

import java.util.List;
import java.util.Optional;

/**
 * @author Alexander Weigl
 * @version 1 (09.05.18)
 */
public interface LookupList<T extends Identifiable> extends List<T> {
    default Optional<T> get(String name) {
        return stream().findFirst().filter(i -> i.getIdentifier().equals(name));
    }

    default Optional<T> getIgnoreCase(String name) {
        return stream().findFirst().filter(i -> i.getIdentifier().equalsIgnoreCase(name));
    }
}

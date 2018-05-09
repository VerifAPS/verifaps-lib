package edu.kit.iti.formal.automation.st;

import lombok.RequiredArgsConstructor;
import lombok.experimental.Delegate;

import java.util.ArrayList;
import java.util.List;

/**
 * @author Alexander Weigl
 * @version 1 (09.05.18)
 */
public class LookupListFactory {
    public static <T extends Identifiable> LookupList<T> create() {
        return create(new ArrayList<>());
    }

    public static <T extends Identifiable> LookupList<T> create(List<T> list) {
        return new LookupListWrapper(list);
    }

    @RequiredArgsConstructor
    private static class LookupListWrapper<T extends Identifiable> implements LookupList<T> {
        @Delegate
        private final List<T> seq;
    }
}

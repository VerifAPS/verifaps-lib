package edu.kit.iti.formal.exteta.model;

import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by weigl on 10.12.16.
 */
public class Region extends State {
    List<State> sub = new ArrayList<>();

    public Region(int id) {
        super(id);
    }

    public List<State> getStates() {
        return sub;
    }

    @Override
    public int count() {
        return sub.stream().mapToInt(State::count).sum();
    }


    public List<State> flat() {
        return sub.stream()
                .flatMap((a) -> a.flat().stream())
                .collect(Collectors.toList());
    }
}

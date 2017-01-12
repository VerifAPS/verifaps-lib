package edu.kit.iti.formal.stvs.model.table;

/**
 * Created by philipp on 10.01.17.
 */
public class ConcreteDuration {

    private int duration;
    private int beginCycle;

    public ConcreteDuration(int duration) {
        this.duration = duration;
    }

    public int getDuration() {
        return duration;
    }

    public int getEndCycle() {return -1;}

    public String toString() {
        return null;
    }
}

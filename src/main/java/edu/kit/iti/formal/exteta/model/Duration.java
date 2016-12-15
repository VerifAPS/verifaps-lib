package edu.kit.iti.formal.exteta.model;

/**
 * Created by weigl on 10.12.16.
 */
public class Duration {
    public int lower;
    public int upper;

    public Duration() {
    }

    public Duration(int l, int u) {
        lower = l;
        upper = u;
    }

    public boolean isUnbounded() {
        return upper == -1;
    }

    public boolean isOneStep() {
        return fixedStep() && upper == 1;
    }

    public boolean skipable() {
        return lower == 0;
    }

    public int maxCounterValue() {
        return Math.max(lower, upper) + 1;
    }

    public boolean fixedStep() {
        return upper == lower;
    }

    public int getLower() {
        return lower;
    }

    public int getUpper() {
        return upper;
    }
}

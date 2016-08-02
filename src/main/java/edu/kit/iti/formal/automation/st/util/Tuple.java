package edu.kit.iti.formal.automation.st.util;

/**
 * Created by weigl on 13.06.14.
 */
public class Tuple<S, T> {
    public final S a;
    public final T b;

    public Tuple(S a, T b) {
        this.a = a;
        this.b = b;
    }

    public static <T, S> Tuple<T, S> make(T a, S b) {
        return new Tuple(a, b);
    }
}

package edu.kit.iti.formal.stvs.model.table;

import java.util.function.Consumer;

/**
 * Created by philipp on 09.01.17.
 */
public interface StringEditable {

    String getAsString();

    void setFromString(String input);

    void addStringListener(Consumer<String> listener);
}

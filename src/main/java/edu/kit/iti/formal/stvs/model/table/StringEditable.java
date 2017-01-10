package edu.kit.iti.formal.stvs.model.table;

import java.util.function.Consumer;

/**
 * Created by philipp on 09.01.17.
 */
public interface StringEditable {

    String getUserInputString();

    void setUserInputString(String input);

    void addUserInputStringListener(Consumer<String> listener);
}

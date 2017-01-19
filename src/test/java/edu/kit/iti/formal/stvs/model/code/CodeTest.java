package edu.kit.iti.formal.stvs.model.code;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import org.junit.Test;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by Philipp on 19.01.2017.
 */
public class CodeTest {

    private final Code code = new Code();

    @Test
    public void testIsEmptyInitially() {
        assertEquals("", code.sourcecodeProperty().get());
    }

    @Test
    public void testSourcecodeListenable() {
        BooleanProperty sourcecodeChanged = new SimpleBooleanProperty(false);
        code.sourcecodeProperty().addListener(change -> sourcecodeChanged.set(true));
        code.sourcecodeProperty().set("TYPE months := (jan, feb) END_TYPE");
        assertEquals("Sourcecode changed", true, sourcecodeChanged.get());
    }

    @Test
    public void testTokensExist() {
        code.sourcecodeProperty().set("TYPE is a keyword END_TYPE");
        assertTrue(code.tokensProperty().get().size() > 0);
    }
}

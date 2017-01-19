package edu.kit.iti.formal.stvs.model.code;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import org.junit.Test;

import static org.junit.Assert.assertEquals;

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
        code.sourcecode().addListener(change -> sourcecodeChanged.set(true));
        assertEquals("Sourcecode changed", true, sourcecodeChanged.get());
    }
}

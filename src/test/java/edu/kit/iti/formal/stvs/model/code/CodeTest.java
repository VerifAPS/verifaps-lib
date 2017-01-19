package edu.kit.iti.formal.stvs.model.code;

import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import org.antlr.v4.runtime.Token;
import org.junit.Test;

import java.util.List;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by Philipp on 19.01.2017.
 */
public class CodeTest {

    private final Code code = new Code();
    private final Code exampleCode = new Code("stfile.st", "THIS IS SPARTA");

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
        List<? extends Token> tokens = code.tokensBinding().getValue();
        System.out.println(tokens);
        assertTrue(tokens.size() > 0);
    }

    @Test
    public void testTokensConcatenated() {
        String source = exampleCode.sourcecodeProperty().get();
        List<? extends Token> tokens = exampleCode.tokensBinding().getValue();
        String tokensConcatenated = tokens.stream()
                .map(Token::getText)
                .reduce("", String::concat);
        assertEquals("Lexer tokens concatenated are source code", source, tokensConcatenated);
    }
}

package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.NullableProperty;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import javafx.beans.property.BooleanProperty;
import javafx.beans.property.SimpleBooleanProperty;
import org.antlr.v4.runtime.Token;
import org.junit.Ignore;
import org.junit.Test;

import java.io.InputStream;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static org.junit.Assert.assertEquals;
import static org.junit.Assert.assertTrue;

/**
 * Created by Philipp on 19.01.2017.
 */
public class CodeTest {

  private final Code code = new Code();
  private final Code exampleCode = new Code("stfile.st", "THIS IS SPARTA");
  private final Code enumDefinition = loadCodeFromFile("define_type.st");

  private static String convertStreamToString(InputStream is) {
    java.util.Scanner s = new java.util.Scanner(is, "UTF-8").useDelimiter("\\A");
    return s.hasNext() ? s.next() : "";
  }

  private static Code loadCodeFromFile(String filename) {
    return new Code(
        filename,
        convertStreamToString(CodeTest.class.getResourceAsStream(filename)));
  }

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

  @Ignore // Bug in the Parser? Enums dont get all possible values assigned...
  @Test
  public void testParsedCodeTypeExtraction() {
    NullableProperty<ParsedCode> parsed = enumDefinition.parsedCodeProperty();
    assertEquals("Find all defined Types", 3, parsed.get().getDefinedTypes().size());

    Set<Type> expectedDefinedTypes = new HashSet<>();
    expectedDefinedTypes.add(TypeBool.BOOL);
    expectedDefinedTypes.add(TypeInt.INT);
    expectedDefinedTypes.add(new TypeEnum("MY_ENUM",
        Arrays.asList("possible", "values", "enum")));
    assertEquals(expectedDefinedTypes, parsed.get().getDefinedTypes());
  }

  @Ignore // same bug problem
  @Test
  public void testParsedCodeIOVariableExtraction() {
    NullableProperty<ParsedCode> parsed = enumDefinition.parsedCodeProperty();
    assertEquals("Find all defined IOVariables", 5, parsed.get().getDefinedVariables().size());

    TypeEnum myEnum = new TypeEnum("MY_ENUM", Arrays.asList("possible", "values", "enum"));

    Set<CodeIoVariable> expectedVariables = new HashSet<>();
    expectedVariables.add(new CodeIoVariable(VariableCategory.INPUT, TypeBool.BOOL, "active"));
    expectedVariables.add(new CodeIoVariable(VariableCategory.INPUT, TypeInt.INT, "number"));
    expectedVariables.add(new CodeIoVariable(VariableCategory.INPUT, myEnum, "my_enum"));
    expectedVariables.add(new CodeIoVariable(VariableCategory.OUTPUT, myEnum, "my_output"));
    expectedVariables.add(new CodeIoVariable(VariableCategory.OUTPUT, TypeBool.BOOL, "seriously"));

    assertEquals(expectedVariables, parsed.get().getDefinedVariables());
  }
}

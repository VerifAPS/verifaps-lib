package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import org.antlr.v4.runtime.Token;
import org.apache.commons.io.IOUtils;
import org.junit.Ignore;
import org.junit.Test;

import java.io.IOException;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import static edu.kit.iti.formal.stvs.model.TestUtils.assertCollectionsEqual;
import static org.junit.Assert.*;

/**
 * Created by Philipp on 19.01.2017.
 */
public class CodeTest {


  private final Code code = new Code();
  private final Code enumDefinition = loadCodeFromFile("define_type.st");
  private final Code invalidCode = loadCodeFromFile("invalidCode.st");
  private final Code simpleCode = new Code("simpleCode.st", "simple sourcecode");
  private final Code simpleCorrectCode = loadCodeFromFile("simpleCorrectCode.st");


  public static Code loadCodeFromFile(String filename) {
    try {
      return new Code(
          filename,
          IOUtils.toString(CodeTest.class.getResourceAsStream(filename), "UTF-8"));
    } catch (IOException e) {
      throw new RuntimeException(e);
    }
  }

  @Test
  public void testIsEmptyInitially() {
    assertEquals("", code.getSourcecode());
  }

  @Test
  public void testTokensExist() {
    code.updateSourcecode("TYPE is a keyword END_TYPE");
    List<? extends Token> tokens = code.getTokens();
    System.out.println(tokens);
    assertTrue(tokens.size() > 0);
  }

  @Test
  @Ignore
  public void testUnicodeChars() {
    code.updateSourcecode("öüäß");
    List<? extends Token> tokens = code.getTokens();
    System.out.println(tokens);
    assertTrue(!tokens.isEmpty());
  }

  @Test
  public void testTokensConcatenated() {
    String source = enumDefinition.getSourcecode();
    List<? extends Token> tokens = enumDefinition.getTokens();
    String tokensConcatenated = tokens.stream()
        .map(Token::getText)
        .reduce("", String::concat);
    assertEquals("Lexer tokens concatenated are source code", source, tokensConcatenated);
  }

  @Test
  public void testParsedCodeTypeExtraction() {
    ParsedCode parsed = enumDefinition.getParsedCode();
    assertEquals("Find all defined Types", 3, parsed.getDefinedTypes().size());

    Type myEnum = new TypeEnum("MY_ENUM", Arrays.asList("possible", "values", "enum"));
    Set<Type> expectedDefinedTypes = new HashSet<>();
    expectedDefinedTypes.add(TypeBool.BOOL);
    expectedDefinedTypes.add(TypeInt.INT);
    expectedDefinedTypes.add(myEnum);
    assertCollectionsEqual(expectedDefinedTypes, parsed.getDefinedTypes());
  }

  @Test
  public void testParsedCodeIOVariableExtraction() {
    ParsedCode parsed = enumDefinition.getParsedCode();
    assertEquals("Find all defined IOVariables", 7, parsed.getDefinedVariables().size());

    Type myEnum = new TypeEnum("MY_ENUM", Arrays.asList("possible", "values", "enum"));
    Set<CodeIoVariable> expectedVariables = new HashSet<>();
    expectedVariables.add(new CodeIoVariable(VariableCategory.INPUT, "BOOL", "active"));
    expectedVariables.add(new CodeIoVariable(VariableCategory.INPUT, "INT", "number"));
    expectedVariables.add(new CodeIoVariable(VariableCategory.INPUT, myEnum.getTypeName(), "my_enum"));
    expectedVariables.add(new CodeIoVariable(VariableCategory.OUTPUT, myEnum.getTypeName(), "my_output"));
    expectedVariables.add(new CodeIoVariable(VariableCategory.OUTPUT, "BOOL", "seriously"));
    expectedVariables.add(new CodeIoVariable(VariableCategory.LOCAL, myEnum.getTypeName(),"my_enum_local"));
    expectedVariables.add(new CodeIoVariable(VariableCategory.INOUT, "BOOL", "active_inout"));
    assertCollectionsEqual(expectedVariables, parsed.getDefinedVariables());
  }

  @Test
  public void testParsedCodeBlocks() {
    FoldableCodeBlock expectedBlock = new FoldableCodeBlock(5, 27);
    assertEquals(expectedBlock, enumDefinition.getParsedCode().getFoldableCodeBlocks().get(0));
    assertEquals(1, enumDefinition.getParsedCode().getFoldableCodeBlocks().size());
    assertEquals(5, enumDefinition.getParsedCode().getFoldableCodeBlocks().get(0).getStartLine());
    assertEquals(27, enumDefinition.getParsedCode().getFoldableCodeBlocks().get(0).getEndLine());
  }

  @Test
  public void testInvalidCode() {
    assertNotNull(invalidCode.getSyntaxErrors().size());
  }

  @Test
  public void testEquals() {
    assertEquals(enumDefinition, enumDefinition);
    assertEquals(loadCodeFromFile("define_type.st"), enumDefinition);
    assertNotEquals(invalidCode, enumDefinition);
    assertNotEquals(null, enumDefinition);
  }

  @Test
  public void testHashCode() {
    assertEquals(enumDefinition.hashCode(), enumDefinition.hashCode());
    assertEquals(loadCodeFromFile("define_type.st").hashCode(), enumDefinition.hashCode());
    assertNotEquals(invalidCode.hashCode(), enumDefinition.hashCode());
  }
}

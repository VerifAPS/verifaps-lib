package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.st.ast.*;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;

import java.util.*;
import java.util.function.Consumer;

/**
 * Created by philipp on 09.01.17.
 */
public class ParsedCode {

  private static class TypeDeclarationVisitor extends DefaultVisitor<Void> {
    private Set<Type> definedTypes;

    TypeDeclarationVisitor() {
      this.definedTypes = new HashSet<>();
      this.definedTypes.add(TypeBool.BOOL);
      this.definedTypes.add(TypeInt.INT);
    }

    @Override
    public Void visit(TypeDeclarations decls) {
      decls.stream().forEach(decl -> decl.visit(this));
      return null;
    }

    @Override
    public Void visit(EnumerationTypeDeclaration enumType) {
      TypeEnum type = new TypeEnum(enumType.getTypeName(), enumType.getAllowedValues());
      this.definedTypes.add(type);
      return null;
    }

    public Set<Type> getDefinedTypes() {
      return definedTypes;
    }

  }

  private static class VariableVisitor extends DefaultVisitor<Void> {
    private Set<CodeIoVariable> definedVariables;
    private Map<String, Type> definedTypes;

    VariableVisitor(Map<String, Type> definedTypes) {
      this.definedVariables = new HashSet<>();
      this.definedTypes = definedTypes;
    }

    @Override
    public Void visit(FunctionDeclaration function) {
      function.getLocalScope().getLocalVariables().entrySet().forEach(variableEntry -> {
        //String varName = variableEntry.getKey();
        VariableDeclaration varDecl = variableEntry.getValue();
        Type type = definedTypes.get(varDecl.getDataTypeName());
        VariableCategory category;
        switch (varDecl.getType()) {
          case VariableDeclaration.INPUT:
            category = VariableCategory.INPUT;
            break;
          case VariableDeclaration.OUTPUT:
            category = VariableCategory.OUTPUT;
            break;
          default:
            // Don't create variables for other types than INPUT or OUTPUT
            //TODO: recognize INOUT or other variables
            return;
        }
        this.definedVariables.add(new CodeIoVariable(category, type, varDecl.getName()));
      });
      return null;
    }

    public Set<CodeIoVariable> getDefinedVariables() {
      return definedVariables;
    }
  }

  private static class BlockVisitor extends DefaultVisitor<Void> {
    private List<FoldableCodeBlock> foldableCodeBlocks;

    BlockVisitor() {
      this.foldableCodeBlocks = new ArrayList<>();
    }

    @Override
    public Void visit(FunctionDeclaration function) {
      FoldableCodeBlock newBlock = new FoldableCodeBlock(function.getStartPosition().getLineNumber(), function.getEndPosition().getLineNumber());
      this.foldableCodeBlocks.add(newBlock);
      return null;
    }

    public List<FoldableCodeBlock> getFoldableCodeBlocks() {
      return this.foldableCodeBlocks;
    }
  }

  private List<FoldableCodeBlock> foldableCodeBlocks;
  private Set<CodeIoVariable> definedVariables;
  private Set<Type> definedTypes;

  public ParsedCode(List<FoldableCodeBlock> foldableCodeBlocks, Set<CodeIoVariable> definedVariables, Set<Type> definedTypes) {
    this.foldableCodeBlocks = foldableCodeBlocks;
    this.definedVariables = definedVariables;
    this.definedTypes = definedTypes;
  }

  public static void parseCode(String input,
                               Consumer<List<? extends Token>> tokenListener,
                               Consumer<List<SyntaxError>> syntaxErrors,
                               Consumer<ParsedCode> parsedCodeListener) {
    try {
      IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(input));
      tokenListener.accept(lexer.getAllTokens());
      lexer.reset();

      IEC61131Parser parser = new IEC61131Parser(new CommonTokenStream(lexer));
      SyntaxErrorListener syntaxErrorListener = new SyntaxErrorListener();
      parser.addErrorListener(syntaxErrorListener);
      syntaxErrors.accept(syntaxErrorListener.getSyntaxErrors());

      TopLevelElements ast = new TopLevelElements(parser.start().ast);

      // Find types in parsed code
      TypeDeclarationVisitor typeVisitor = new TypeDeclarationVisitor();
      ast.visit(typeVisitor);
      Map<String, Type> definedTypesByName = new HashMap<>();
      typeVisitor.getDefinedTypes().forEach(type -> definedTypesByName.put(type.getTypeName(), type));

      // Find IoVariables in parsed code
      VariableVisitor variableVisitor = new VariableVisitor(definedTypesByName);
      ast.visit(variableVisitor);

      // Find code blocks in parsed code
      BlockVisitor blockVisitor = new BlockVisitor();
      ast.visit(blockVisitor);
      List<FoldableCodeBlock> foldableCodeBlocks = blockVisitor.getFoldableCodeBlocks();

      parsedCodeListener.accept(
          new ParsedCode(
              foldableCodeBlocks,
              variableVisitor.getDefinedVariables(),
              typeVisitor.getDefinedTypes())
      );
      // GOTTA CATCH 'EM ALL! *sings*
    } catch (Exception exception) {
      exception.printStackTrace();
    }

  }

  public List<FoldableCodeBlock> getFoldableCodeBlocks() {
    return foldableCodeBlocks;
  }

  public Set<CodeIoVariable> getDefinedVariables() {
    return definedVariables;
  }

  public Set<Type> getDefinedTypes() {
    return definedTypes;
  }

}

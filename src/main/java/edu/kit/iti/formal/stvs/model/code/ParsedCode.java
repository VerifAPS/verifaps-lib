package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.automation.parser.IEC61131Lexer;
import edu.kit.iti.formal.automation.parser.IEC61131Parser;
import edu.kit.iti.formal.automation.parser.IECParseTreeToAST;
import edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration;
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration;
import edu.kit.iti.formal.automation.st.ast.ProgramDeclaration;
import edu.kit.iti.formal.automation.st.ast.Top;
import edu.kit.iti.formal.automation.st.ast.TopLevelElements;
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Optional;
import java.util.stream.Collectors;

import org.antlr.v4.runtime.ANTLRInputStream;
import org.antlr.v4.runtime.CommonTokenStream;
import org.antlr.v4.runtime.Token;

/**
 * Represents the formal model of source code (extracted from {@link Code}).
 * @author Lukas Fritsch
 */
public class ParsedCode {

  /**
   * A visitor for type declarations. Builds a list of types which have been declared in the code.
   */
  private static class TypeDeclarationVisitor extends DefaultVisitor<Void> {
    private List<Type> definedTypes;

    TypeDeclarationVisitor() {
      this.definedTypes = new ArrayList<>();
      this.definedTypes.add(TypeBool.BOOL);
      this.definedTypes.add(TypeInt.INT);
    }

    @Override
    public Void visit(TypeDeclarations decls) {
      decls.stream().forEach(decl -> decl.accept(this));
      return null;
    }

    @Override
    public Void visit(EnumerationTypeDeclaration enumType) {
      if (!enumType.getAllowedValues().isEmpty()) {
        TypeEnum type = new TypeEnum(enumType.getTypeName(),
                enumType.getAllowedValues().stream().map(Token::getText).collect(Collectors.toList()));
        this.definedTypes.add(type);
      }
      return null;
    }

    public List<Type> getDefinedTypes() {
      return definedTypes;
    }

  }

  /**
   * A visitor which visits a {@link ProgramDeclaration} and builds a list of i/o variables
   * defined therein.
   */
  private static class VariableVisitor extends DefaultVisitor<Void> {
    private List<CodeIoVariable> definedVariables = new ArrayList<>();

    @Override
    public Void visit(ProgramDeclaration program) {
      program.getLocalScope().getLocalVariables().entrySet().forEach(variableEntry -> {
        // String varName = variableEntry.getKey();
        VariableDeclaration varDecl = variableEntry.getValue();
        Optional<VariableCategory> category = getCategoryFromDeclaration(varDecl);
        Optional<String> dataTypeName = Optional.ofNullable(varDecl.getDataTypeName());
        if (category.isPresent() && dataTypeName.isPresent()) {
          this.definedVariables
              .add(new CodeIoVariable(category.get(), dataTypeName.get(), varDecl.getName()));
        }
      });
      return null;
    }

    private Optional<VariableCategory> getCategoryFromDeclaration(VariableDeclaration varDecl) {
      if (varDecl.isConstant()) {
        return Optional.empty();

      }
      switch (varDecl.getType()) {
        case VariableDeclaration.INPUT:
          return Optional.of(VariableCategory.INPUT);
        case VariableDeclaration.OUTPUT:
          return Optional.of(VariableCategory.OUTPUT);
        case VariableDeclaration.LOCAL:
          return Optional.of(VariableCategory.LOCAL);
        case VariableDeclaration.INOUT:
          return Optional.of(VariableCategory.INOUT);
        default:
          return Optional.empty();
      }
    }

    public List<CodeIoVariable> getDefinedVariables() {
      return definedVariables;
    }
  }

  /**
   * A visitor which visits {@link FunctionDeclaration}s and builds a list of
   * {@link FoldableCodeBlock}s, where each function declaration corresponds to one block.
   */
  private static class BlockVisitor extends DefaultVisitor<Void> {
    private List<FoldableCodeBlock> foldableCodeBlocks;

    BlockVisitor() {
      this.foldableCodeBlocks = new ArrayList<>();
    }

    private void addBlock(Top topElement) {
      foldableCodeBlocks.add(new FoldableCodeBlock(topElement.getStartPosition().getLineNumber(),
          topElement.getEndPosition().getLineNumber()));
    }

    @Override
    public Void visit(FunctionDeclaration function) {
      addBlock(function);
      return null;
    }

    @Override
    public Void visit(ProgramDeclaration program) {
      addBlock(program);
      return null;
    }

    List<FoldableCodeBlock> getFoldableCodeBlocks() {
      return this.foldableCodeBlocks;
    }
  }

  private List<FoldableCodeBlock> foldableCodeBlocks;
  private List<CodeIoVariable> definedVariables;
  private List<Type> definedTypes;

  /**
   * Creates a parsed code.
   *
   * @param foldableCodeBlocks list of codeblocks
   * @param definedVariables list of all defined variables (in the source code)
   * @param definedTypes list of all defined types (in the source code)
   */
  public ParsedCode(List<FoldableCodeBlock> foldableCodeBlocks,
      List<CodeIoVariable> definedVariables, List<Type> definedTypes) {
    this.foldableCodeBlocks = foldableCodeBlocks;
    this.definedVariables = definedVariables;
    this.definedTypes = definedTypes;
  }

  /**
   * Parses a code. The handlers and listeners provided as parameters are called with the results
   * of the parsing; i.e. the parsedCodeListener is called with the resulting {@link ParsedCode},
   * the parsedTokenHandler is called with the list of parsed tokens etc.
   *
   * @param input the source code to parse
   * @param parsedTokenHandler a handler for lexed tokens
   * @param syntaxErrorsListener listener for a list of {@link SyntaxError}s
   * @param parsedCodeListener listener for parsed code.
   */
  public static void parseCode(String input, ParsedTokenHandler parsedTokenHandler,
      ParsedSyntaxErrorHandler syntaxErrorsListener, ParsedCodeHandler parsedCodeListener) {
    SyntaxErrorListener syntaxErrorListener = new SyntaxErrorListener();

    IEC61131Lexer lexer = lex(input, parsedTokenHandler, syntaxErrorListener);

    TopLevelElements ast = parse(new CommonTokenStream(lexer), syntaxErrorListener);

    syntaxErrorsListener.accept(syntaxErrorListener.getSyntaxErrors());

    // Find types in parsed code
    TypeDeclarationVisitor typeVisitor = new TypeDeclarationVisitor();
    ast.accept(typeVisitor);
    Map<String, Type> definedTypesByName = new HashMap<>();
    typeVisitor.getDefinedTypes()
        .forEach(type -> definedTypesByName.put(type.getTypeName(), type));

    // Find IoVariables in parsed code
    VariableVisitor variableVisitor = new VariableVisitor();
    ast.accept(variableVisitor);

    // Find code blocks in parsed code
    BlockVisitor blockVisitor = new BlockVisitor();
    ast.accept(blockVisitor);
    List<FoldableCodeBlock> foldableCodeBlocks = blockVisitor.getFoldableCodeBlocks();

    parsedCodeListener.accept(new ParsedCode(foldableCodeBlocks,
        variableVisitor.getDefinedVariables(), typeVisitor.getDefinedTypes()));
  }

  /**
   * Parses a token stream.
   * @param tokenStream The token stream to parse
   * @param syntaxErrorListener The listener to invoke on syntax errors
   * @return The AST constructed from the token stream
   */
  private static TopLevelElements parse(CommonTokenStream tokenStream, SyntaxErrorListener
      syntaxErrorListener) {
    IEC61131Parser parser = new IEC61131Parser(tokenStream);
    parser.removeErrorListeners();
    parser.addErrorListener(syntaxErrorListener);

    return (TopLevelElements) parser.start().accept(new IECParseTreeToAST());
  }

  /**
   * Lex a given code.
   * @param input The code to lex
   * @param parsedTokenHandler Is called with the resulting list of tokens
   * @param syntaxErrorListener Is given to the lexer (and invoked on syntax errors)
   * @return The lexer used for lexing
   */
  private static IEC61131Lexer lex(String input, ParsedTokenHandler parsedTokenHandler,
                                   SyntaxErrorListener syntaxErrorListener) {
    IEC61131Lexer lexer = new IEC61131Lexer(new ANTLRInputStream(input));
    lexer.removeErrorListeners();
    lexer.addErrorListener(syntaxErrorListener);
    parsedTokenHandler.accept(lexer.getAllTokens());
    lexer.reset();
    return lexer;
  }

  public List<FoldableCodeBlock> getFoldableCodeBlocks() {
    return foldableCodeBlocks;
  }

  public List<CodeIoVariable> getDefinedVariables() {
    return definedVariables;
  }

  public List<Type> getDefinedTypes() {
    return definedTypes;
  }
}

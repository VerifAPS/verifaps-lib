package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration;
import edu.kit.iti.formal.automation.st.ast.FunctionDeclaration;
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations;
import edu.kit.iti.formal.automation.st.ast.VariableDeclaration;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;

import java.util.*;

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

  public static ParsedCode parseCode(String input) {

    try {
      TypeDeclarationVisitor typeVisitor = new TypeDeclarationVisitor();
      IEC61131Facade.file(input).visit(typeVisitor);

      Set<Type> definedTypes = typeVisitor.getDefinedTypes();
      Map<String, Type> definedTypesByName = new HashMap<>();
      definedTypes.forEach(type -> definedTypesByName.put(type.getTypeName(), type));

      VariableVisitor variableVisitor = new VariableVisitor(definedTypesByName);
      IEC61131Facade.file(input).visit(variableVisitor);

      BlockVisitor blockVisitor = new BlockVisitor();
      IEC61131Facade.file(input).visit(blockVisitor);
      List<FoldableCodeBlock> foldableCodeBlocks;
      foldableCodeBlocks = blockVisitor.getFoldableCodeBlocks();

      return new ParsedCode(foldableCodeBlocks, variableVisitor.getDefinedVariables(), typeVisitor.getDefinedTypes());
    } catch (Exception exception) {
      return null;
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

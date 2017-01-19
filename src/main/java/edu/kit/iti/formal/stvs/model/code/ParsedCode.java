package edu.kit.iti.formal.stvs.model.code;

import edu.kit.iti.formal.automation.IEC61131Facade;
import edu.kit.iti.formal.automation.st.ast.EnumerationTypeDeclaration;
import edu.kit.iti.formal.automation.st.ast.TypeDeclarations;
import edu.kit.iti.formal.automation.visitors.DefaultVisitor;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Created by philipp on 09.01.17.
 */
public class ParsedCode {

  private static class TypeDeclarationVisitor extends DefaultVisitor<Void> {
    private Set<Type> definedTypes;

    TypeDeclarationVisitor() {
      this.definedTypes = new HashSet<>();
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

  private List<FoldableCodeBlock> foldableCodeBlocks;
  private Set<CodeIoVariable> definedVariables;
  private Set<Type> definedTypes;

  public ParsedCode(List<FoldableCodeBlock> foldableCodeBlocks, Set<CodeIoVariable> definedVariables, Set<Type> definedTypes) {
    this.foldableCodeBlocks = foldableCodeBlocks;
    this.definedVariables = definedVariables;
    this.definedTypes = definedTypes;
  }

  public static ParsedCode parseCode(String input) {
    TypeDeclarationVisitor visitor = new TypeDeclarationVisitor();

    Set<CodeIoVariable> definedVariables = new HashSet<>();
    List<FoldableCodeBlock> foldableCodeBlocks = new ArrayList<>();

    try {
      IEC61131Facade.file(input).visit(visitor);
      return new ParsedCode(foldableCodeBlocks, definedVariables, visitor.getDefinedTypes());
    } catch (Exception e) {
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

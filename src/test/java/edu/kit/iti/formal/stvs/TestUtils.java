package edu.kit.iti.formal.stvs;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConstraintSpecImporter;
import edu.kit.iti.formal.stvs.model.common.*;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeEnum;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.ValidSpecification;
import edu.kit.iti.formal.stvs.model.table.problems.ConstraintSpecificationValidator;
import edu.kit.iti.formal.stvs.model.table.problems.SpecProblem;
import javafx.beans.property.SimpleObjectProperty;

import java.io.InputStream;
import java.net.InetAddress;
import java.net.UnknownHostException;
import java.util.ArrayList;
import java.util.Collections;
import java.util.List;
import java.util.stream.Collectors;

/**
 * Created by bal on 10.02.17.
 */
public class TestUtils {

  public static ValidSpecification importValidSpec(InputStream source, TypeEnum... enumTypes) {
    List<Type> typeContext = new ArrayList<>();
    typeContext.add(TypeInt.INT);
    typeContext.add(TypeBool.BOOL);
    for (TypeEnum enumType : enumTypes) {
      typeContext.add(enumType);
    }
    return importValidSpec(source, typeContext);
  }

  public static ValidSpecification importValidSpec(
      InputStream source,
      List<Type> typeContext) {
    try {
      ConstraintSpecification constraintSpec = ImporterFacade.importConstraintSpec(source, ImporterFacade.ImportFormat.XML);
      List<ValidFreeVariable> validFreeVariables = importValidFreeVariables(
          constraintSpec.getFreeVariableList(), typeContext);
      ConstraintSpecificationValidator validator = new ConstraintSpecificationValidator(
          new SimpleObjectProperty<>(typeContext),
          new SimpleObjectProperty<>(new ArrayList<>()),
          new SimpleObjectProperty<>(validFreeVariables),
          constraintSpec
      );
      ValidSpecification validSpec = validator.getValidSpecification();
      if (validSpec == null) {
        System.err.println("ConstraintSpecification could not be validated:");
        validator.problemsProperty().get().stream().map(SpecProblem::getErrorMessage).forEach(System.err::println);
        throw new RuntimeException("Couldn't validate Specification");
      }
      return validSpec;
    } catch (ImportException cause) {
      throw new RuntimeException(cause);
    }
  }

  public static List<ValidFreeVariable> importValidFreeVariables(InputStream source, TypeEnum... enumTypes) {
    List<Type> typeContext = new ArrayList<>();
    typeContext.add(TypeInt.INT);
    typeContext.add(TypeBool.BOOL);
    for (TypeEnum enumType : enumTypes) {
      typeContext.add(enumType);
    }
    try {
      return importValidFreeVariables(
          ImporterFacade.importConstraintSpec(source, ImporterFacade.ImportFormat.XML).getFreeVariableList(),
          typeContext);
    } catch (ImportException ex) {
      throw new RuntimeException(ex);
    }
  }

  public static List<ValidFreeVariable> importValidFreeVariables(FreeVariableList freeVariableList, List<Type> typeContext) {
    FreeVariableListValidator validator = new FreeVariableListValidator(
        new SimpleObjectProperty<>(typeContext), freeVariableList);
    if (!validator.problemsProperty().get().isEmpty()) {
      System.err.println("Could not validate free variables:");
      validator.problemsProperty().get().entrySet().stream()
          .map(entry -> entry.getKey() + " -> "
              + entry.getValue().stream()
              .map(FreeVariableProblem::getGUIMessage)
              .collect(Collectors.toList()))
          .forEach(System.err::println);
      throw new RuntimeException("Couldn't validate");
    }
    return validator.validFreeVariablesProperty().get();
  }
}

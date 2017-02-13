package edu.kit.iti.formal.stvs;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.logic.io.xml.XmlConstraintSpecImporter;
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
import edu.kit.iti.formal.stvs.model.common.ValidIoVariable;
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

/**
 * Created by bal on 10.02.17.
 */
public class TestUtils {
  /**
   *
   * @return The user's config or null if config does not exist
   */
  public static GlobalConfig getUserConfig() throws UnknownHostException, ImportException {
    String configFilename = "/userConfigs/" + InetAddress.getLocalHost()
        .getHostName() + ".xml";
    InputStream userConfig = TestUtils.class.getResourceAsStream(configFilename);
    if (userConfig != null) {
      return ImporterFacade.importConfig(userConfig, ImporterFacade.ImportFormat.XML);
    } else {
      return null;
    }
  }

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
      ConstraintSpecification constraintSpec = ImporterFacade.importSpec(source, ImporterFacade.ImportFormat.XML);
      FreeVariableListValidator freevarValidator = new FreeVariableListValidator(
          new SimpleObjectProperty<>(typeContext),
          constraintSpec.getFreeVariableList()
      );
      List<ValidFreeVariable> validFreeVariables = freevarValidator.validFreeVariablesProperty().get();
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
}

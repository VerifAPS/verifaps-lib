package edu.kit.iti.formal.stvs;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.common.FreeVariableList;
import edu.kit.iti.formal.stvs.model.common.FreeVariableListValidator;
import edu.kit.iti.formal.stvs.model.common.FreeVariableProblem;
import edu.kit.iti.formal.stvs.model.common.ValidFreeVariable;
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
import javafx.collections.FXCollections;
import javafx.stage.FileChooser;
import org.junit.Assume;
import org.mockito.Mockito;
import org.mockito.stubbing.OngoingStubbing;
import org.powermock.api.mockito.PowerMockito;

import java.io.File;
import java.io.InputStream;
import java.net.URL;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.concurrent.TimeUnit;
import java.util.stream.Collectors;

import static org.mockito.ArgumentMatchers.any;
import static org.testfx.util.WaitForAsyncUtils.sleep;

/**
 * Created by bal on 10.02.17.
 */
public class TestUtils {

  /**
   * Tolerance for floating-point rounding errors when doing assertEquals() with doubles
   */
  public static final double EPSILON = 0.001;

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
              .map(FreeVariableProblem::getGuiMessage)
              .collect(Collectors.toList()))
          .forEach(System.err::println);
      throw new RuntimeException("Couldn't validate");
    }
    return validator.validFreeVariablesProperty().get();
  }

  public static void gimmeTime() {
    sleep(5, TimeUnit.SECONDS);
  }

  public static void mockFiles(URL ... urls) throws Exception {
    List<File> files = Arrays.stream(urls)
        .map(URL::getPath)
        .map(File::new)
        .collect(Collectors.toList());
    FileChooser chooser = Mockito.mock(FileChooser.class);
    OngoingStubbing<File> stub = Mockito.when(chooser.showOpenDialog(any()));
    for (File file : files) {
      stub = stub.thenReturn(file);
    }
    Mockito.when(chooser.getExtensionFilters()).thenReturn(FXCollections.observableList(new ArrayList<>()));
    PowerMockito.whenNew(FileChooser.class).withAnyArguments().thenReturn(chooser);
  }

    private static void assumeFileExists(String message, String executable) {
        Assume.assumeTrue(message, new File(executable).exists());
    }

    public static void assumeZ3Exists() {
        assumeFileExists(
                "The z3 command is not set or a non-existing file. Tests are skipped!",
                GlobalConfig.autoloadConfig().getZ3Path());
    }

    public static void assumeNuXmvExists() {
        assumeFileExists(
                "The nuxmv command is not set or a non-existing file. Tests are skipped!",
                GlobalConfig.autoloadConfig().getNuxmvFilename());
    }

    public static void assumeGetetaExists() {
        String[] toks = GlobalConfig.autoloadConfig().getGetetaCommand()
                .split(" ");
        assumeFileExists(
                "The geteta command is not set or a non-existing file. Tests are skipped!",
                toks[0]);
    }
}
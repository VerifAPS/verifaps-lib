package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.code.ParsedCode;
import edu.kit.iti.formal.stvs.model.common.CodeIoVariable;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import edu.kit.iti.formal.stvs.view.editor.EditorPaneController;
import edu.kit.iti.formal.stvs.view.spec.SpecificationsPaneController;
import edu.kit.iti.formal.stvs.view.spec.VerificationStartedEvent;
import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.beans.value.ObservableValue;

import java.util.Arrays;
import java.util.Collections;
import java.util.List;

/**
 * Created by csicar on 09.01.17.
 */
public class StvsRootController implements Controller {

  private final StvsRootView view;
  private final StvsRootModel stvsRootModel;
  private final ObjectProperty<List<Type>> types;
  private final ObjectProperty<List<CodeIoVariable>> ioVars;
  private final SpecificationsPaneController specificationsPaneController;
  private EditorPaneController editorPaneController;

  public StvsRootController(StvsRootModel rootModel) {
    this.stvsRootModel = rootModel;
    this.editorPaneController = new EditorPaneController(
        stvsRootModel.getScenario().getCode(),
        stvsRootModel.getGlobalConfig()
    );

    this.types = new SimpleObjectProperty<>(typesFromCode(stvsRootModel.getScenario().getCode().getParsedCode()));
    this.ioVars = new SimpleObjectProperty<>(ioVarsFromCode(stvsRootModel.getScenario().getCode().getParsedCode()));
    this.specificationsPaneController = new SpecificationsPaneController(
        stvsRootModel.getHybridSpecifications(),
        stvsRootModel.getScenario().verificationState(),
        types,
        ioVars
    );

    this.stvsRootModel.getScenario().codeObjectProperty().addListener(this::onCodeChange);
    this.stvsRootModel.getScenario().getCode().parsedCodeProperty().addListener(this::parsedCodeChange);

    this.view = new StvsRootView(
        editorPaneController.getView(),
        specificationsPaneController.getView());

    view.addEventHandler(VerificationStartedEvent.EVENT_TYPE,
        this::onVerificationStartRequested);
  }

  private void onVerificationStartRequested(VerificationStartedEvent event) {
    System.out.println("Starting verificatioN!!!");
    //stvsRootModel.getScenario().verify(event.getConstraintSpec());
  }

  private List<CodeIoVariable> ioVarsFromCode(ParsedCode parsedCode) {
    if (parsedCode == null) {
      return Collections.emptyList();
    }
    return parsedCode.getDefinedVariables();
  }

  private List<Type> typesFromCode(ParsedCode parsedCode) {
    if (parsedCode == null) {
      return Arrays.asList(TypeInt.INT, TypeBool.BOOL);
    }
    return parsedCode.getDefinedTypes();
  }

  public StvsRootView getView() {
    return view;
  }

  private void onCodeChange(ObservableValue<? extends Code> observableValue, Code old, Code code) {
    editorPaneController = new EditorPaneController(code, stvsRootModel.getGlobalConfig());
    code.parsedCodeProperty().addListener(this::parsedCodeChange);
    view.setEditor(editorPaneController.getView());
  }

  private void parsedCodeChange(ObservableValue<? extends ParsedCode> o, ParsedCode old, ParsedCode parsedCode) {
    if (parsedCode != null) {
      types.set(typesFromCode(parsedCode));
      ioVars.set(ioVarsFromCode(parsedCode));
    }
  }

}

package edu.kit.iti.formal.stvs.view.menu;

import static edu.kit.iti.formal.stvs.view.common.FileChooserFactory.FileType.ANY;
import static edu.kit.iti.formal.stvs.view.common.FileChooserFactory.FileType.CODE;
import static edu.kit.iti.formal.stvs.view.common.FileChooserFactory.FileType.SESSION;
import static edu.kit.iti.formal.stvs.view.common.FileChooserFactory.FileType.SPECIFICATION;

import edu.kit.iti.formal.stvs.logic.examples.ExamplesFacade;
import edu.kit.iti.formal.stvs.logic.io.ExportException;
import edu.kit.iti.formal.stvs.logic.io.ExporterFacade;
import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.StvsRootModel;
import edu.kit.iti.formal.stvs.model.code.Code;
import edu.kit.iti.formal.stvs.model.examples.Example;
import edu.kit.iti.formal.stvs.model.table.ConstraintSpecification;
import edu.kit.iti.formal.stvs.model.table.HybridSpecification;
import edu.kit.iti.formal.stvs.view.Controller;
import edu.kit.iti.formal.stvs.view.ViewUtils;
import edu.kit.iti.formal.stvs.view.common.AlertFactory;
import edu.kit.iti.formal.stvs.view.common.FileChooserFactory;

import java.io.File;
import java.io.IOException;
import java.net.URL;
import java.util.Optional;

import javafx.beans.property.ObjectProperty;
import javafx.beans.property.SimpleObjectProperty;
import javafx.event.ActionEvent;
import javafx.scene.control.*;
import javafx.scene.control.Dialog;
import javafx.scene.control.MenuItem;
import javafx.stage.FileChooser;

/**
 * Created by csicar on 10.01.17. Controller for the MenuBar at the top of the window does just fire
 * to the root controller
 *
 * @author Carsten Csiky
 */
public class StvsMenuBarController implements Controller {
    private StvsMenuBar view;
    private ObjectProperty<StvsRootModel> rootModel;
    private ObjectProperty<File> lastDirectory = new SimpleObjectProperty<>(
            new File("."));

    /**
     * create a StvsMenuBarController; the parameters will be modified.
     *
     * @param rootModel the applications root model
     */
    public StvsMenuBarController(ObjectProperty<StvsRootModel> rootModel) {
        // set own properties
        this.rootModel = rootModel;

        // create view
        this.view = new StvsMenuBar();

        rootModel.get().getHistory().getFilenames()
                .addListener(new HistoryFilenamesChangeListener());
        // Fill history menu
        updateHistoryMenu();

        // add listener
        view.newCode.setOnAction(this::createNewCode);
        view.newSpec.setOnAction(this::createNewSpec);
        view.open.setOnAction(this::openFile);
        view.openSession.setOnAction(this::openSession);
        view.openCode.setOnAction(this::openCode);
        view.openSpec.setOnAction(this::openSpec);
        view.saveAll.setOnAction(this::saveAll);
        view.saveSessionAs.setOnAction(this::saveSessionAs);
        view.saveCode.setOnAction(this::saveCode);
        view.saveSpec.setOnAction(this::saveSpec);
        view.config.setOnAction(this::openConfigDialog);
        view.wizard.setOnAction(this::openWizard);
        view.about.setOnAction(this::openAboutDialog);

        //popluate examples
        for (Example ex : ExamplesFacade.getExamples()) {
            final Example a = ex;
            final MenuItem mex = new MenuItem(ex.getName());
            mex.setOnAction((value) -> this.openExample(a));
            mex.setMnemonicParsing(true);
            Tooltip.install(mex.getGraphic(), new Tooltip(ex.getDescription()));
            view.examples.getItems().add(mex);
        }
    }

    void openExample(Example ex) {
        URL url = ex.getSessionFile();
        try {
            StvsRootModel session = ImporterFacade
                    .importSession(url.openStream(),
                            ImporterFacade.ImportFormat.XML,
                            rootModel.get().getGlobalConfig(),
                            rootModel.get().getHistory());

            session.setFilename(null);
            this.rootModel.set(session);

            if (null != ex.getHtmlHelp()) {
                ViewUtils.openHelpText("Help for " + ex.getName() + " Example",
                        ex.getHtmlHelp());
            }

        } catch (ImportException e) {
            e.printStackTrace();
        } catch (IOException e) {
            e.printStackTrace();
        }

    }

    private void updateHistoryMenu() {
        view.openRecentItems.clear();
        for (String filename : rootModel.get().getHistory().getFilenames()) {
            MenuItem newItem = new MenuItem(filename);
            newItem.setOnAction(
                    (actionEvent -> doOpenFile(new File(filename))));
            view.openRecentItems.add(newItem);
        }
        view.openRecent.getItems().clear();
        view.openRecent.getItems().addAll(view.openRecentItems);
    }


    private void openWizard(ActionEvent actionEvent) {
        new WelcomeWizard(rootModel.get().getGlobalConfig()).showAndWait();
    }


    private void doOpenFile(File file) {
        try {
            ImporterFacade.importFile(file, rootModel.get().getGlobalConfig(),
                    rootModel.get().getHistory(), (hybridSpecification) -> {
                        // handle hybridspecification
                        rootModel.get().getHybridSpecifications()
                                .add(hybridSpecification);
                    }, (rootModel) -> {
                        // handle rootModel
                        rootModel.setWorkingdir(file.getParentFile());
                        rootModel.setFilename(file.getName());
                        this.rootModel.setValue(rootModel);
                    }, (code -> {
                        // handle code
                        rootModel.get().getScenario().setCode(code);
                    }));
            rootModel.get().getHistory().addFilename(file.getAbsolutePath());
        } catch (IOException | ImportException ex) {
            AlertFactory.createAlert(Alert.AlertType.ERROR, "File Open Error",
                    "An error occurred while opening a file.",
                    "The file " + file.getAbsolutePath()
                            + " could not be opened.", ex.getMessage())
                    .showAndWait();
        }
    }


    private void saveSessionAs(ActionEvent actionEvent) {
        FileChooser fileChooser = FileChooserFactory
                .createSaveFileChooser(SESSION,
                        rootModel.get().getWorkingdir());
        File chosenFile = fileChooser
                .showSaveDialog(view.getScene().getWindow());
        if (chosenFile != null) {
            handleSaveAll(chosenFile);
            setWorkingDir(chosenFile);
        }
    }

    private void createNewSpec(ActionEvent actionEvent) {
        rootModel.get().addNewHybridSpec();
    }

    private void createNewCode(ActionEvent actionEvent) {
        boolean clear = false;
        if (!rootModel.get().getScenario().getCode().getSourcecode().isEmpty()) {
            ButtonType save = new ButtonType("Save", ButtonBar.ButtonData.APPLY);
            Alert request = new Alert(Alert.AlertType.CONFIRMATION, "Do you really want to throw away your code?",
                    ButtonType.YES, save, ButtonType.NO);
            //request.initOwner();
            Optional<ButtonType> answer = request.showAndWait();
            if (answer.isPresent()) {
                if (answer.get() == save) {
                    clear = saveCode(actionEvent);
                }
                if (answer.get() == ButtonType.YES) {
                    clear = true;
                }
            }
            if (clear) this.rootModel.get().getScenario().setCode(new Code());
        }
    }

    private void openConfigDialog(ActionEvent t) {
        ConfigDialogManager dialogManager = new ConfigDialogManager(
                rootModel.get().getGlobalConfig());
        dialogManager.showAndWait();
    }


    private void openAboutDialog(ActionEvent actionEvent) {
        Dialog dialog = new Dialog();
        AboutDialogPane pane = new AboutDialogPane();
        dialog.setTitle("About");
        dialog.setDialogPane(pane);

        dialog.showAndWait();
    }

    private void openCode(ActionEvent t) {
        FileChooser fileChooser = FileChooserFactory
                .createOpenFileChooser(CODE, rootModel.get().getWorkingdir());
        File chosenFile = fileChooser
                .showOpenDialog(view.getScene().getWindow());
        if (chosenFile == null) {
            return;
        }
        try {
            Code code = ImporterFacade.importStCode(chosenFile);
            this.rootModel.get().getScenario().setCode(code);
            this.rootModel.get().getHistory()
                    .addFilename(chosenFile.getAbsolutePath());
            setWorkingDir(chosenFile);
        } catch (IOException e) {
            AlertFactory.createAlert(e).showAndWait();
        }
    }

    private void openSession(ActionEvent t) {
        FileChooser fileChooser = FileChooserFactory
                .createOpenFileChooser(SESSION,
                        rootModel.get().getWorkingdir());
        File chosenFile = fileChooser
                .showOpenDialog(view.getScene().getWindow());

        if (chosenFile == null) {
            return;
        }
        try {
            StvsRootModel model = ImporterFacade
                    .importSession(chosenFile, ImporterFacade.ImportFormat.XML,
                            rootModel.get().getGlobalConfig(),
                            rootModel.get().getHistory());
            setWorkingDir(chosenFile);
            model.setFilename(chosenFile.getName());
            this.rootModel.set(model);
            this.rootModel.get().getHistory()
                    .addFilename(chosenFile.getAbsolutePath());
        } catch (IOException | ImportException exception) {
            AlertFactory.createAlert(exception).showAndWait();
        }
    }

    private void openSpec(ActionEvent t) {
        FileChooser fileChooser = FileChooserFactory
                .createOpenFileChooser(SPECIFICATION,
                        rootModel.get().getWorkingdir());
        File chosenFile = fileChooser
                .showOpenDialog(view.getScene().getWindow());
        if (chosenFile == null) {
            return;
        }
        try {
            HybridSpecification spec = ImporterFacade
                    .importHybridSpec(chosenFile,
                            ImporterFacade.ImportFormat.XML);
            this.rootModel.get().getHybridSpecifications().add(spec);
            this.rootModel.get().getHistory()
                    .addFilename(chosenFile.getAbsolutePath());
            setWorkingDir(chosenFile);
        } catch (IOException | ImportException e) {
            AlertFactory.createAlert(e).showAndWait();
        }
    }

    private void openFile(ActionEvent t) {
        FileChooser fileChooser = FileChooserFactory
                .createOpenFileChooser(ANY, rootModel.get().getWorkingdir());
        File chosenFile = fileChooser
                .showOpenDialog(view.getScene().getWindow());

        if (chosenFile == null) {
            return;
        }
        doOpenFile(chosenFile);
        setWorkingDir(chosenFile);
    }

    private void saveAll(ActionEvent t) {
        if (this.rootModel.get().getFilename().isEmpty()) {
            FileChooser fileChooser = FileChooserFactory
                    .createSaveFileChooser(SESSION,
                            rootModel.get().getWorkingdir());
            File chosenFile = fileChooser
                    .showSaveDialog(view.getScene().getWindow());
            if (chosenFile != null) {
                handleSaveAll(chosenFile);
            }
        } else {
            handleSaveAll(new File(rootModel.get().getWorkingdir(),
                    rootModel.get().getFilename()));
        }
    }

    private void handleSaveAll(File path) {
        try {
            rootModel.get().setWorkingdir(path.getParentFile());
            rootModel.get().setFilename(path.getName());
            ExporterFacade.exportSession(rootModel.get(),
                    ExporterFacade.ExportFormat.XML, path);
        } catch (IOException | ExportException exception) {
            AlertFactory.createAlert(exception).showAndWait();
        }
    }

    private boolean saveCode(ActionEvent t) {
        // Set the code filename, if no filename set yet
        Code code = rootModel.get().getScenario().getCode();
        if (code.getFilename().isEmpty()) {
            FileChooser fileChooser = FileChooserFactory
                    .createSaveFileChooser(CODE,
                            rootModel.get().getWorkingdir());
            File chosenFile = fileChooser
                    .showSaveDialog(view.getScene().getWindow());
            if (chosenFile == null) {
                return false;
            }
            code.setFilename(chosenFile.getAbsolutePath());
        }
        // Export the code to the file
        try {
            ExporterFacade.exportCode(code, false);
            return true;
        } catch (IOException e) {
            AlertFactory.createAlert(e).showAndWait();
            return false;
        }
    }

    private void saveSpec(ActionEvent t) {
        try {
            ConstraintSpecification spec = rootModel.get().getScenario()
                    .getActiveSpec();
            if (spec == null) { // There is no active specification tab open yet
                AlertFactory.createAlert(Alert.AlertType.ERROR,
                        "Save Specification", "No specification available.", "")
                        .showAndWait();
            } else {
                FileChooser fileChooser = FileChooserFactory
                        .createSaveFileChooser(SPECIFICATION,
                                rootModel.get().getWorkingdir());
                File specFile = fileChooser
                        .showSaveDialog(view.getScene().getWindow());
                ExporterFacade.exportSpec(spec, ExporterFacade.ExportFormat.XML,
                        specFile);
            }
        } catch (ExportException | IOException e) {
            AlertFactory.createAlert(e).showAndWait();
        }
    }

    @Override
    public StvsMenuBar getView() {
        return view;
    }

    public void setWorkingDir(File workingDir) {
        rootModel.get().setWorkingdir(workingDir.isDirectory() ?
                workingDir :
                workingDir.getParentFile());
    }

    private class HistoryFilenamesChangeListener
            implements javafx.collections.ListChangeListener<String> {

        @Override
        public void onChanged(Change<? extends String> change) {
            updateHistoryMenu();
        }
    }
}

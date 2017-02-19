package edu.kit.iti.formal.stvs.view.spec.table;

import edu.kit.iti.formal.stvs.model.common.SpecIoVariable;
import edu.kit.iti.formal.stvs.model.common.VariableCategory;
import edu.kit.iti.formal.stvs.model.table.problems.ColumnProblem;
import javafx.beans.Observable;
import javafx.beans.binding.Bindings;
import javafx.beans.property.SimpleStringProperty;
import javafx.beans.property.StringProperty;
import javafx.beans.value.ObservableValue;
import javafx.geometry.Pos;
import javafx.scene.control.Label;
import javafx.scene.control.Tooltip;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import org.reactfx.value.Var;

import java.util.Collection;

/**
 * Created by philipp on 11.02.17.
 * @author Philipp
 */
public class ColumnHeader extends VBox {

  private final Label categoryLabel;
  private final Label columnNameLabel;
  private final Label columnTypeLabel;
  private final Label typeOfLabel;
  private final HBox varDescriptionHbox;
  private final Tooltip problemTooltip;

  public ColumnHeader(SpecIoVariable specIoVariable) {
    this.categoryLabel = new Label(specIoVariable.getCategory().toString());
    this.columnNameLabel = new Label(specIoVariable.getName());
    this.columnTypeLabel = new Label(specIoVariable.getType());
    this.typeOfLabel = new Label(" : ");
    this.problemTooltip = new Tooltip("");

    categoryLabel.textProperty().bind(Bindings.convert(specIoVariable.categoryProperty()));
    columnNameLabel.textProperty().bind(specIoVariable.nameProperty());
    columnTypeLabel.textProperty().bind(specIoVariable.typeProperty());

    String inout = specIoVariable.getCategory().toString().toLowerCase();

    categoryLabel.getStyleClass().addAll("spec-column-header", "category-label", inout);
    columnNameLabel.getStyleClass().addAll("spec-column-header", "name-label");
    columnTypeLabel.getStyleClass().addAll("spec-column-header", "type-label");
    typeOfLabel.getStyleClass().addAll("spec-column-header", "type-of-label");
    problemTooltip.getStyleClass().addAll("spec-column-header", "problem-tooltip");

    specIoVariable.categoryProperty().addListener(this::updateInOutClass);

    this.getStyleClass().addAll("spec-column-header", inout);
    this.setAlignment(Pos.CENTER);

    this.varDescriptionHbox = new HBox(columnNameLabel, typeOfLabel, columnTypeLabel);
    this.varDescriptionHbox.setAlignment(Pos.CENTER);

    this.getChildren().addAll(categoryLabel, varDescriptionHbox);
  }

  private void updateInOutClass(ObservableValue<? extends VariableCategory> o, VariableCategory oldCategory, VariableCategory category) {
    String old = oldCategory.toString().toLowerCase();
    String newCategory = category.toString().toLowerCase();
    getStyleClass().remove(old);
    getStyleClass().add(newCategory);

    categoryLabel.getStyleClass().remove(old);
    categoryLabel.getStyleClass().add(newCategory);
  }

  public Label getCategoryLabel() {
    return categoryLabel;
  }

  public Label getColumnNameLabel() {
    return columnNameLabel;
  }

  public Label getColumnTypeLabel() {
    return columnTypeLabel;
  }

  public void configureProblems(Collection<ColumnProblem> problems) {
    this.getStyleClass().remove("spec-column-problem");
    this.getStyleClass().add("spec-column-problem");
    problemTooltip.setText(
        problems.stream()
            .map(ColumnProblem::getErrorMessage)
            .reduce((left, right) -> left + "\n\n" + right)
            .orElse(""));
    Tooltip.install(this, problemTooltip);
  }

  public void resetProblems() {
    this.getStyleClass().remove("spec-column-problem");
    Tooltip.uninstall(this, problemTooltip);
  }
}

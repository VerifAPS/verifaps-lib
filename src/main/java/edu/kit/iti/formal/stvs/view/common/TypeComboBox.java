package edu.kit.iti.formal.stvs.view.common;

import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.util.ListTypeConverter;
import javafx.beans.property.ObjectProperty;
import javafx.beans.value.ObservableValue;
import javafx.collections.ObservableList;
import javafx.scene.control.ComboBox;
import javafx.util.StringConverter;

import java.util.List;

/**
 * Created by Philipp on 07.02.2017.
 */
public class TypeComboBox extends ComboBox<Type> {

  private static StringConverter<Type> createTypeConverter(ObjectProperty<List<Type>> codeTypes) {
    return new StringConverter<Type>() {
      @Override
      public String toString(Type type) {
        return type.getTypeName();
      }
      @Override
      public Type fromString(String string) {
        return codeTypes.get().stream()
            .filter(type -> type.getTypeName().equals(string))
            .findFirst()
            .orElse(null);
      }
    };
  }

  private final ObservableList<Type> possibleItems;

  public TypeComboBox(ObjectProperty<List<Type>> codeTypes) {
    super();
    this.possibleItems = ListTypeConverter.makeObservableList(codeTypes);
    setConverter(createTypeConverter(codeTypes));
    setItems(possibleItems);

    codeTypes.addListener(this::codeTypesChanged);
  }

  private void codeTypesChanged(ObservableValue<? extends List<Type>> obs, List<Type> old, List<Type> newCodeTypes) {
    possibleItems.clear();
    possibleItems.addAll(newCodeTypes);
  }
}

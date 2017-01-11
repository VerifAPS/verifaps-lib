package edu.kit.iti.formal.stvs.view.editor;

import javafx.beans.property.StringProperty;
import javafx.scene.layout.HBox;
import javafx.scene.layout.Pane;
import javafx.scene.layout.VBox;
import org.fxmisc.richtext.CodeArea;
import org.fxmisc.richtext.StyleSpans;

import java.util.Collection;
import java.util.List;

/**
 * Created by csicar on 09.01.17.
 *
 */
public class EditorPane extends Pane {
    private StringProperty code;

    /**
     * Contains ButtonList and CodeArea
     */
    private HBox horizontalBox;
    private CodeArea codeArea;
    private VBox buttonList;


    public StringProperty getCodeProperty() {
        return null;
    }

    public String getCode() {
        return code.toString();
    }

    public void setCode(String code) {

    }



    public void setStyleSpans(StyleSpans<Collection<String>> style){

    }

    public CodeArea getCodeArea() {
        return codeArea;
    }

    public VBox getButtonList() {
        return buttonList;
    }
}

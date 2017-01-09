package edu.kit.iti.formal.stvs.view.editor;

import javafx.beans.property.StringProperty;
import javafx.scene.layout.Pane;

/**
 * Created by csicar on 09.01.17.
 */
public class EditorPane extends Pane {
    StringProperty code;
    StyleSpans spans;

    public StringProperty getCodeProperty(){
        return null;
    }

    public String getCode() {
        return code.toString();
    }

    public void setCode(String code) {

    }

    public void setSpans(StyleSpans spans) {

    }

    private void setStylesheet(String url) {

    }
}

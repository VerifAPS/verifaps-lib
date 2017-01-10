package edu.kit.iti.formal.stvs.view.editor;

import edu.kit.iti.formal.stvs.model.code.SourcecodeToken;
import javafx.beans.property.StringProperty;
import javafx.scene.layout.Pane;
import org.fxmisc.richtext.CodeArea;
import org.fxmisc.richtext.StyleSpans;

import java.util.Collection;
import java.util.List;

/**
 * Created by csicar on 09.01.17.
 *
 * Some parts are inspired by examples of the used library:
 * https://github.com/TomasMikula/RichTextFX/blob/a098da6309a0f624052fd1d4d6f5079dd6265fbe/richtextfx-demos/src/main/java/org/fxmisc/richtext/demo/JavaKeywords.java
 */
public class EditorPane extends Pane {
    StringProperty code;
    private CodeArea codeArea;


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
}

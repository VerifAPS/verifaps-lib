package sample;

/**
 * Created by leonk on 09.11.2016.
 */
public class EditorTextStyle {
    public String toCss() {
        return String.join(
                "-fx-font-weight: normal;",
                "-fx-font-size: 16px;",
                "-fx-font-family: monospace"
        );
    }
}

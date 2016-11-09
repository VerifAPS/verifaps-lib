package sample;

import javafx.scene.paint.Color;

import java.util.Random;

/**
 * Created by leonk on 09.11.2016.
 */
public class EditorTextStyle {
    private String style = String.join(
            "-fx-font-weight: normal;",
            "-fx-font-size: 16px;",
            "-fx-font-family: monospace;"
    );

    public String toCss() {
        return style;
    }

    public void appendCss(String s){
        s = s.trim();
        s = " " + s;
        if(!s.endsWith(";")) s += ";";
        style += s;
    }

    public static EditorTextStyle random() {
        EditorTextStyle style = new EditorTextStyle();
        Random rand = new Random();
        Color color = Color.hsb(rand.nextDouble(), 1, 1);
        float randomFloat = rand.nextFloat() * 360;
        style.appendCss("-fx-fill: linear-gradient(to right, hsb("+ randomFloat +",100%,100%),  hsb("+ (randomFloat+180) % 360 +",100%,100%))");
        return style;
    }
}

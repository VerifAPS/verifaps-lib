package edu.kit.iti.formal.stvs.view.menu;

import edu.kit.iti.formal.stvs.StvsApplication;
import edu.kit.iti.formal.stvs.view.common.ActualHyperLink;
import edu.kit.iti.formal.stvs.view.common.HostServiceSingleton;
import javafx.geometry.Insets;
import edu.kit.iti.formal.stvs.StvsVersion;
import javafx.geometry.Pos;
import javafx.scene.control.*;
import javafx.scene.image.Image;
import javafx.scene.image.ImageView;
import javafx.scene.layout.HBox;
import javafx.scene.layout.VBox;
import javafx.scene.text.Font;

/**
 * <p>
 * The Dialog Pane that shows 'About' information.
 * </p>
 * <p>
 * <p>
 * Is created when the user clicks on 'Help' -> 'About' and shows the name and version information,
 * etc.
 * </p>
 * <p>
 * <p>
 * Created by csicar on 16.02.17.
 * </p>
 *
 * @author Carsten Csiky
 */
public class AboutDialogPane extends DialogPane {


  /**
   * Creates the Dialog Pane that displays 'About' information.
   */
  public AboutDialogPane() {
    TabPane tabPane = new TabPane(createAboutTab(), createAcknowledgementsTab());

    tabPane.setPadding(Insets.EMPTY);

    this.setContent(tabPane);
    this.getButtonTypes().addAll(ButtonType.CLOSE);
    this.setContent(tabPane);

  }

  private static HBox createLibrary(String name, String url, String license, String licenseUrl) {
    Hyperlink nameView = new ActualHyperLink(name, url);
    Hyperlink licenseView = new ActualHyperLink(license, licenseUrl);

    HBox hBox = new HBox(nameView, new Label("License: "), licenseView);
    hBox.setAlignment(Pos.CENTER_LEFT);
    return hBox;
  }

  private static Tab createAcknowledgementsTab() {



    VBox libraries = new VBox(
        createLibrary(
            "iec61131lang",
            "https://github.com/VerifAPS/iec61131lang",
            "GPLv3",
            "https://www.gnu.org/licenses/gpl-3.0.en.html"
        ),

        createLibrary(
            "Apache Commons Collections",
            "https://commons.apache.org/proper/commons-collections/",
            "Apache License Version 2.0",
            "https://www.apache.org/licenses/LICENSE-2.0"
        ),

        createLibrary(
            "jsexp",
            "https://github.com/julianmendez/jsexp",
            "LGPLv3",
            "https://www.gnu.org/licenses/lgpl-3.0.txt"
        ),

        createLibrary(
            "Apache Commons Lang",
            "https://commons.apache.org/proper/commons-lang/",
            "Apache License Version 2.0",
            "https://www.apache.org/licenses/LICENSE-2.0"
        ),

        createLibrary(
          "Apache Commons IO",
            "https://commons.apache.org/proper/commons-io/",
            "Apache License Version 2.0",
            "https://www.apache.org/licenses/LICENSE-2.0"
        ),

        createLibrary(
            "gson",
            "https://github.com/google/gson",
            "Apache License Version 2.0",
            "https://github.com/google/gson/blob/master/LICENSE"
        ),

        createLibrary(
            "richtextfx",
            "https://github.com/TomasMikula/RichTextFX",
            "BSD 2-Clause License and GPLv2 with the Classpath Exception",
            "https://github.com/TomasMikula/RichTextFX/blob/master/LICENSE"
        ),

        createLibrary(
            "antlr",
            "http://www.antlr.org/",
            "BSD 3-Clause License",
            "https://github.com/antlr/antlr4/blob/master/LICENSE.txt"
        ),

        createLibrary(
            "JAXB",
            "https://jaxb.java.net/",
            "CDDLv1.1 and GPLv2",
            "https://glassfish.java.net/public/CDDL+GPL_1_1.html"
        )
    );

    Tab tab = new Tab("Acknowledgements", libraries);
    tab.setClosable(false);
    return tab;
  }

  private static Tab createAboutTab() {

    Image logo = new Image(StvsApplication.class.getResourceAsStream("logo.png"));
    ImageView logoView = new ImageView(logo);
    Label name = new Label("Structured Text Verification Studio");
    name.setFont(Font.font("DejaVu Sans Mono", 30));
    Label version = new Label(
            "Version: " + StvsVersion.getVersion() + " built from "
                    + StvsVersion.getBuildId());

    Hyperlink license = new ActualHyperLink(
        "License: GPLv3",
        "https://github.com/VerifAPS/stvs/blob/master/LICENSE"
    );

    Hyperlink homepage = new ActualHyperLink(
        "Homepage",
        "http://formal.iti.kit.edu/stvs"
    );

    Hyperlink repo = new ActualHyperLink(
        "Repository",
        "https://github.com/verifaps/stvs"
    );

    HBox versionAndLicense =  new HBox(version, license);
    versionAndLicense.setAlignment(Pos.CENTER);

    HBox links = new HBox(homepage, repo);
    links.setAlignment(Pos.CENTER);

    VBox aboutBox = new VBox(
        logoView,
        name,
        versionAndLicense,
        links
    );
    aboutBox.setAlignment(Pos.CENTER);
    aboutBox.setPadding(new Insets(20.0, 15.0, 20.0, 15.0));
    Tab tab = new Tab("About", aboutBox);
    tab.setClosable(false);
    return tab;
  }
}

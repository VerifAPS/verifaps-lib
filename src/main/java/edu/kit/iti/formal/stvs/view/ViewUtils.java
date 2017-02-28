package edu.kit.iti.formal.stvs.view;

import edu.kit.iti.formal.stvs.view.editor.EditorPane;
import javafx.scene.Node;
import javafx.scene.Parent;
import javafx.scene.transform.Affine;
import javafx.scene.transform.Transform;

/**
 * Created by leonk on 05.02.2017.
 *
 * @author Benjamin Alt
 */
public class ViewUtils {
  /**
   * @param rootOfCalculation Any node in a scene graph
   * @param child             A direct/indirect child of rootOfCalculation
   * @return A Transformation between coordinates of child and rootOfCalculation
   */
  public static Transform calculateTransformRelativeTo(Node rootOfCalculation, Node child) {
    if (child.getScene() == null) {
      throw new IllegalStateException("Child is not displayed in any scene currently.");
    }
    if (child.getParent() == null) {
      throw new IllegalStateException("rootOfCalculation is not in the scenegraph between root node and child.");
    }
    if (child == rootOfCalculation) {
      return new Affine();
    }
    Transform parentTransform = calculateTransformRelativeTo(rootOfCalculation, child.getParent());
    return child.getLocalToParentTransform().createConcatenation(parentTransform);
  }

  /**
   * adds the style sheet (name "style.css" and located in the same package) to the given parent
   * and sets the css-id for the parent
   * @param parent parent that should be setup
   */
  public static void setupView(Parent parent) {
    setupView(parent, "style.css");
  }

  /**
   * adds the style sheet (located in the same package) to the given parent
   * and sets the css-id for the parent
   * @param parent parent that should be setup
   * @param stylesheet stylesheet's name in the package
   */
  public static void setupView(Parent parent, String stylesheet) {
    parent.getStylesheets().add(parent.getClass().getResource(stylesheet).toExternalForm());

    setupId(parent);
  }



  /**
   * sets the css-id for the parent.
   * @param parent parent that should be setup
   */
  public static void setupId(Parent parent) {
    parent.setId(parent.getClass().getSimpleName());
  }

}

package edu.kit.iti.formal.stvs.model.common;

import edu.kit.iti.formal.stvs.model.expressions.ValueInt;
import edu.kit.iti.formal.stvs.model.expressions.Type;
import edu.kit.iti.formal.stvs.model.expressions.TypeBool;
import edu.kit.iti.formal.stvs.model.expressions.TypeInt;
import org.junit.Test;

import java.util.ArrayList;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Created by leonk on 18.01.2017.
 */
public class FreeVariableListTest {
  @Test
  public void testMain() {
    FreeVariableList empty = new FreeVariableList(variables);
    empty.getVariables().add(new FreeVariable("Test1", TypeBool.BOOL));
    empty.getVariables().add(new FreeVariable("Test2", TypeInt.INT));
    empty.getVariables().add(new FreeVariable("Test3", TypeBool.BOOL));
    Map<String, Type> variableContext = empty.getVariableContext();
    assertEquals(variableContext.get("Test1"), TypeBool.BOOL);
    assertEquals(variableContext.get("Test2"), TypeInt.INT);
    assertEquals(variableContext.get("Test3"), TypeBool.BOOL);
  }

  @Test
  public void testFromExistingList() throws IllegalValueTypeException {
    List<FreeVariable> list = new ArrayList<>();
    list.add(new FreeVariable("Test1", TypeInt.INT, new ValueInt(5)));
    list.add(new FreeVariable("Test2", TypeInt.INT, new ValueInt(6)));
    list.add(new FreeVariable("Test3", TypeInt.INT, new ValueInt(7)));
    FreeVariableList freeVariables = new FreeVariableList(list);
    assertEquals(3, freeVariables.getVariables().size());
  }

  @Test
  public void testSameNameProblems(){
    FreeVariableList freeVariableList = new FreeVariableList(variables);
    FreeVariable free1 = new FreeVariable("Test", TypeBool.BOOL);
    FreeVariable free2 = new FreeVariable("Test", TypeInt.INT);
    freeVariableList.getVariables().addAll(
        free1,
        free2
    );
    assertEquals(1, freeVariableList.getProblems().size());
    free1.setName("Test2");
    assertEquals(0, freeVariableList.getProblems().size());
    free1.setName("Test");
    assertEquals(1, freeVariableList.getProblems().size());
    free1.setName("Test2");
    assertEquals(0, freeVariableList.getProblems().size());
    freeVariableList.getVariables().add(new FreeVariable("Test", TypeInt.INT));
    freeVariableList.getVariables().add(new FreeVariable("Test2", TypeInt.INT));
    assertEquals(2, freeVariableList.getProblems().size());
  }

  @Test
  public void testSameNameProblemsRemove(){
    FreeVariableList freeVariableList = new FreeVariableList(variables);
    FreeVariable free1 = new FreeVariable("Test", TypeBool.BOOL);
    FreeVariable free2 = new FreeVariable("Test", TypeInt.INT);
    freeVariableList.getVariables().addAll(
        free1,
        free2
    );
    freeVariableList.getVariables().remove(1);
    assertEquals(0, freeVariableList.getProblems().size());
  }
}
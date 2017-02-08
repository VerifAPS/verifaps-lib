package edu.kit.iti.formal.stvs.logic.specification;

import org.junit.Test;

import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import static org.junit.Assert.*;

/**
 * Created by csicar on 08.02.17.
 */
public class SMTConcretizerTest {
  private Map<Integer, Integer> m_j;


  private void setupMj() {
    m_j = new HashMap<>();
    m_j.put(-1, 0);
    m_j.put(0, 2);
    m_j.put(1, 5);
    m_j.put(2, 5);
  }

  private int sumMj(int n) {
    int accu = 0;
    for (int i = 0; i <= n; i++) {
      accu += m_j.get(i);
    }
    return accu;
  }

  @Test
  public void test() {
    setupMj();
    int maxZ = 2;
    List vars = Arrays.asList("A");



    for (int z = 0; z <= 2; z++) {
      System.out.println("Zeile "+z);
      for (int i = 1; i <= sumMj(z-1); i++) {
        for(int k = 0; k <= m_j.get(z-1); k++) {
          System.out.println("n_"+(z-1)+"="+k+" => "+"A_"+z+","+(-i)+" = "+"A_"+(z-1)+","+(k-i));
        }
      }
    }
  }

}
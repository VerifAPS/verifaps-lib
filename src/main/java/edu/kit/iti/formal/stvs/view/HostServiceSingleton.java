package edu.kit.iti.formal.stvs.view;

import javafx.application.HostServices;

/**
 * Created by csicar on 16.03.17.
 */
public class HostServiceSingleton {
  private static HostServices instance;

  public static void setInstance(HostServices newInstance) {
    if (instance != null) {
      throw new IllegalStateException("already set");
    }
    instance = newInstance;
  }

  public static HostServices getInstance() {
    return instance;
  }
}

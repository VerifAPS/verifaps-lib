package edu.kit.iti.formal.stvs.model.config;

import java.util.Arrays;
import java.util.List;

/**
 * Contains global configuration specified by the user
 */
public class GlobalConfig {

  private List<String> validLanguages = Arrays.asList("EN");

  private int verificationTimeout;
  private int simulationTimeout;
  private int windowHeight;
  private int windowWidth;
  private int editorFontSize;
  private String editorFontFamily;
  private boolean showLineNumbers;
  private String uiLanguage;

  /**
   * Default configuration
   */
  public GlobalConfig() {
    verificationTimeout = 3600;
    simulationTimeout = 60;
    windowHeight = 600;
    windowWidth = 800;
    editorFontSize = 12;
    editorFontFamily = "Courier";
    showLineNumbers = true;
    uiLanguage = "EN";
  }

  /**
   * Get the current verification timeout
   *
   * @return The current verification timeout
   */
  public int getVerificationTimeout() {
    return verificationTimeout;
  }

  /**
   * Get the current simulation timeout
   *
   * @return The current simulation timeout
   */
  public int getSimulationTimeout() {
    return simulationTimeout;
  }

  /**
   * Get the current editor font size
   *
   * @return The current editor font size
   */
  public int getEditorFontSize() {
    return editorFontSize;
  }

  /**
   * Get the current editor font family
   *
   * @return The current editor font family
   */
  public String getEditorFontFamily() {
    return editorFontFamily;
  }

  /**
   * Are line numbers to be shown in the editor?
   *
   * @return Whether line numbers are to be shown in the editor
   */
  public boolean getShowLineNumbers() {
    return showLineNumbers;
  }

  /**
   * What is the current UI language?
   *
   * @return The current UI language
   */
  public String getUiLanguage() {
    return uiLanguage;
  }

  /**
   * Set the current verification timeout
   *
   * @param verificationTimeout The verification timeout to set
   */
  public void setVerificationTimeout(int verificationTimeout) {
    if (verificationTimeout <= 0) {
      throw new IllegalArgumentException("Invalid verification timeout: " + verificationTimeout);
    }
    this.verificationTimeout = verificationTimeout;
  }

  /**
   * Set the current simulation timeout
   *
   * @param simulationTimeout The simulation timeout to set
   */
  public void setSimulationTimeout(int simulationTimeout) {
    if (simulationTimeout <= 0) {
      throw new IllegalArgumentException("Invalid simulation timeout: " + simulationTimeout);
    }
    this.simulationTimeout = simulationTimeout;
  }

  /**
   * Set the current editor font size
   *
   * @param editorFontSize The editor font size to set
   */
  public void setEditorFontSize(int editorFontSize) {
    if (editorFontSize <= 0) {
      throw new IllegalArgumentException("Invalid editor font size: " + editorFontSize);
    }
    this.editorFontSize = editorFontSize;
  }

  /**
   * Set the current editor font family
   *
   * @param editorFontFamily The verification timeout to set
   */
  public void setEditorFontFamily(String editorFontFamily) {
    this.editorFontFamily = editorFontFamily;
  }

  /**
   * Are line numbers to be shown in the editor?
   *
   * @param showLineNumbers Whether line numbers are to be shown in the editor
   */
  public void setShowLineNumbers(boolean showLineNumbers) {
    this.showLineNumbers = showLineNumbers;
  }

  /**
   * Set the current UI language
   *
   * @param uiLanguage
   */
  public void setUiLanguage(String uiLanguage) {
    if (!validLanguages.contains(uiLanguage))  {
      throw new IllegalArgumentException("Input language " + uiLanguage + " is not supported");
    }
    this.uiLanguage = uiLanguage;
  }

  public int getWindowHeight() {
    return windowHeight;
  }

  public void setWindowHeight(int windowHeight) {
    if (windowHeight <= 0) {
      throw new IllegalArgumentException("Illegal window height: " + windowHeight);
    }
    this.windowHeight = windowHeight;
  }

  public int getWindowWidth() {
    return windowWidth;
  }

  public void setWindowWidth(int windowWidth) {
    if (windowWidth <= 0) {
      throw new IllegalArgumentException("Illegal window width: " + windowWidth);
    }
    this.windowWidth = windowWidth;
  }

}

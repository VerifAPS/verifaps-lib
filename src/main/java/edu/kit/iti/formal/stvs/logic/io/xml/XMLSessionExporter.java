package edu.kit.iti.formal.stvs.logic.io.xml;

import edu.kit.iti.formal.stvs.model.STVSRootModel;

import java.io.OutputStream;

/**
 * Created by bal on 11.01.17.
 */
public class XMLSessionExporter extends XMLExporter<STVSRootModel> {
  private XMLConfigExporter configExporter;
  private XMLSpecExporter specExporter;

  @Override
  public OutputStream export(STVSRootModel source) {
    return null;
  }

}

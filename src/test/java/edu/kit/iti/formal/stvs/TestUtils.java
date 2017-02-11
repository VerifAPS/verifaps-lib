package edu.kit.iti.formal.stvs;

import edu.kit.iti.formal.stvs.logic.io.ImportException;
import edu.kit.iti.formal.stvs.logic.io.ImporterFacade;
import edu.kit.iti.formal.stvs.model.config.GlobalConfig;

import java.io.InputStream;
import java.net.InetAddress;
import java.net.UnknownHostException;

/**
 * Created by bal on 10.02.17.
 */
public class TestUtils {
  /**
   *
   * @return The user's config or null if config does not exist
   */
  public static GlobalConfig getUserConfig() throws UnknownHostException, ImportException {
    String configFilename = "/userConfigs/" + InetAddress.getLocalHost()
        .getHostName() + ".xml";
    InputStream userConfig = TestUtils.class.getResourceAsStream(configFilename);
    if (userConfig != null) {
      return ImporterFacade.importConfig(userConfig, ImporterFacade.ImportFormat.XML);
    } else {
      return null;
    }
  }
}

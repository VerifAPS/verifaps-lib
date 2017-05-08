package edu.kit.iti.formal.stvs;

/**
 * @author Alexander Weigl
 * @version 1 (15.04.17)
 */
public class StvsVersion {
    public static String getVersion() {
        return StvsVersion.class.getPackage().getImplementationVersion();
    }

    public static String getBuildId() {
        return StvsVersion.class.getPackage().getSpecificationVersion();
    }

    public static String getName() {
        return StvsVersion.class.getPackage().getName();
    }

}

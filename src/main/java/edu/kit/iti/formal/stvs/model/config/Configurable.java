package edu.kit.iti.formal.stvs.model.config;

/**
 * This interface must be implemented by classes that have an external config object
 */
public interface Configurable<Cnf> {
    public void setConfig(Cnf config);

    public Cnf getConfig();
}

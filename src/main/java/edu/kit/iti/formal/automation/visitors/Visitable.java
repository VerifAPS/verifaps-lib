package edu.kit.iti.formal.automation.visitors;

/**
 * @author weigla
 * @date 24.06.2014
 */
public interface Visitable {
    public <T> T visit(Visitor<T> visitor);
}

package edu.kit.iti.formal.automation.sfclang.ast;

/*-
 * #%L
 * iec61131lang
 * %%
 * Copyright (C) 2016 Alexander Weigl
 * %%
 * This program is free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.sfclang.SFCAstVisitor;

import java.util.*;

/**
 * <p>StepDeclaration class.</p>
 *
 * @author weigl
 * @version $Id: $Id
 */
public class StepDeclaration {
    boolean initial;
    String name;
    Map<String, List<String>> events = new HashMap<>();


    /**
     * <p>isInitial.</p>
     *
     * @return a boolean.
     */
    public boolean isInitial() {
        return initial;
    }

    /**
     * <p>Getter for the field <code>events</code>.</p>
     *
     * @return a {@link java.util.Map} object.
     */
    public Map<String, List<String>> getEvents() {
        return events;
    }

    /**
     * <p>Getter for the field <code>name</code>.</p>
     *
     * @return a {@link java.lang.String} object.
     */
    public String getName() {
        return name;
    }

    /**
     * <p>Setter for the field <code>name</code>.</p>
     *
     * @param name a {@link java.lang.String} object.
     */
    public void setName(String name) {
        this.name = name;
    }

    /**
     * <p>push.</p>
     *
     * @param eventType a {@link java.lang.String} object.
     * @param actionName a {@link java.lang.String} object.
     */
    public void push(String eventType, String actionName) {
        if (!events.containsKey(eventType)) {
            events.put(eventType, new ArrayList<>());
        }

        events.get(eventType).add(actionName);
    }

    /**
     * <p>accept.</p>
     *
     * @param v a {@link edu.kit.iti.formal.automation.sfclang.SFCAstVisitor} object.
     * @param <T> a T object.
     * @return a T object.
     */
    public <T> T visit(SFCAstVisitor<T> v) {
        return v.visit(this);
    }

    /**
     * <p>isInitialStep.</p>
     *
     * @return a boolean.
     */
    public boolean isInitialStep() {
        return initial;
    }

    /**
     * <p>Setter for the field <code>initial</code>.</p>
     *
     * @param initial a boolean.
     */
    public void setInitial(boolean initial) {
        initial = initial;
    }

    public void addEvent(String type, String... actionNames) {
        if (!getEvents().containsKey(type)) {
            getEvents().put(type, new ArrayList<>());
        }
        getEvents().get(type).addAll(Arrays.asList(actionNames));
    }
}

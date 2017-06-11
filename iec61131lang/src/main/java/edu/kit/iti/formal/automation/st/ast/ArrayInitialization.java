package edu.kit.iti.formal.automation.st.ast;

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

import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedException;
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * Created by weigl on 13.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class ArrayInitialization<T> extends Initialization
        implements List<Initialization>, Visitable {
    private List<Initialization> initValues = new ArrayList<>();

    /**
     * {@inheritDoc}
     */
    @Override public boolean add(Initialization initialization) {
        return initValues.add(initialization);
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean remove(Object o) {
        return initValues.remove(o);
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean containsAll(Collection<?> c) {
        return initValues.containsAll(c);
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean addAll(Collection<? extends Initialization> c) {
        return initValues.addAll(c);
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean addAll(int index,
            Collection<? extends Initialization> c) {
        return initValues.addAll(index, c);
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean removeAll(Collection<?> c) {
        return initValues.removeAll(c);
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean retainAll(Collection<?> c) {
        return initValues.retainAll(c);
    }

    /**
     * {@inheritDoc}
     */
    @Override public void replaceAll(UnaryOperator<Initialization> operator) {
        initValues.replaceAll(operator);
    }

    /**
     * {@inheritDoc}
     */
    @Override public void sort(Comparator<? super Initialization> c) {
        initValues.sort(c);
    }

    /**
     * {@inheritDoc}
     */
    @Override public void clear() {
        initValues.clear();
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean equals(Object o) {
        return initValues.equals(o);
    }

    /**
     * {@inheritDoc}
     */
    @Override public int hashCode() {
        return initValues.hashCode();
    }

    /**
     * {@inheritDoc}
     */
    @Override public Initialization get(int index) {
        return initValues.get(index);
    }

    /**
     * {@inheritDoc}
     */
    @Override public Initialization set(int index, Initialization element) {
        return initValues.set(index, element);
    }

    /**
     * {@inheritDoc}
     */
    @Override public void add(int index, Initialization element) {
        initValues.add(index, element);
    }

    /**
     * {@inheritDoc}
     */
    @Override public Initialization remove(int index) {
        return initValues.remove(index);
    }

    /**
     * {@inheritDoc}
     */
    @Override public int indexOf(Object o) {
        return initValues.indexOf(o);
    }

    /**
     * {@inheritDoc}
     */
    @Override public int lastIndexOf(Object o) {
        return initValues.lastIndexOf(o);
    }

    /**
     * {@inheritDoc}
     */
    @Override public ListIterator<Initialization> listIterator() {
        return initValues.listIterator();
    }

    /**
     * {@inheritDoc}
     */
    @Override public ListIterator<Initialization> listIterator(int index) {
        return initValues.listIterator(index);
    }

    /**
     * {@inheritDoc}
     */
    @Override public List<Initialization> subList(int fromIndex, int toIndex) {
        return initValues.subList(fromIndex, toIndex);
    }

    /**
     * {@inheritDoc}
     */
    @Override public Spliterator<Initialization> spliterator() {
        return initValues.spliterator();
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean removeIf(
            Predicate<? super Initialization> filter) {
        return initValues.removeIf(filter);
    }

    /**
     * {@inheritDoc}
     */
    @Override public Stream<Initialization> stream() {
        return initValues.stream();
    }

    /**
     * {@inheritDoc}
     */
    @Override public Stream<Initialization> parallelStream() {
        return initValues.parallelStream();
    }

    /**
     * {@inheritDoc}
     */
    @Override public void forEach(Consumer<? super Initialization> action) {
        initValues.forEach(action);
    }

    /**
     * {@inheritDoc}
     */
    @Override public int size() {
        return initValues.size();
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean isEmpty() {
        return initValues.isEmpty();
    }

    /**
     * {@inheritDoc}
     */
    @Override public boolean contains(Object o) {
        return initValues.contains(o);
    }

    /**
     * {@inheritDoc}
     */
    @Override public Iterator<Initialization> iterator() {
        return initValues.iterator();
    }

    /**
     * {@inheritDoc}
     */
    @Override public Object[] toArray() {
        return initValues.toArray();
    }

    /**
     * {@inheritDoc}
     */
    @Override public <T> T[] toArray(T[] a) {
        return initValues.toArray(a);
    }

    /**
     * {@inheritDoc}
     */
    @Override public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override public Any dataType(LocalScope localScope)
            throws VariableNotDefinedException, TypeConformityException {
        //TODO
        return null;
    }

    @Override public ArrayInitialization clone() {
        ArrayInitialization ai = new ArrayInitialization();
        forEach(i -> ai.add(i.clone()));
        return ai;
    }
}

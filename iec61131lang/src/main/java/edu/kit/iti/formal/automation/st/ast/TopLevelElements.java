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

import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.EqualsAndHashCode;
import lombok.ToString;

import java.util.*;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * <p>TopLevelElements class.</p>
 *
 * @author weigla (04.07.2014)
 */
@EqualsAndHashCode
@ToString
public class TopLevelElements extends Top implements List<TopLevelElement> {
    private List<TopLevelElement> list = new ArrayList<>();

    /**
     * <p>Constructor for TopLevelElements.</p>
     */
    public TopLevelElements() {
    }

    /**
     * <p>Constructor for TopLevelElements.</p>
     *
     * @param elements a {@link java.util.List} object.
     */
    public TopLevelElements(List<TopLevelElement> elements) {
        list = new ArrayList<>(elements);
    }

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> sev) {//empty
        list.stream().forEach(a -> a.accept(sev));
        return null;
    }

    @Override
    public TopLevelElements copy() {
        TopLevelElements es = new TopLevelElements();
        forEach(e -> es.add(e.copy()));
        return es;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int size() {
        return list.size();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean isEmpty() {
        return list.isEmpty();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean contains(Object o) {
        return list.contains(o);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Iterator<TopLevelElement> iterator() {
        return list.iterator();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Object[] toArray() {
        return list.toArray();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public <T> T[] toArray(T[] a) {
        return list.toArray(a);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean add(TopLevelElement topLevelElement) {
        return list.add(topLevelElement);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean remove(Object o) {
        return list.remove(o);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean containsAll(Collection<?> c) {
        return list.containsAll(c);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean addAll(Collection<? extends TopLevelElement> c) {
        return list.addAll(c);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean addAll(int index, Collection<? extends TopLevelElement> c) {
        return list.addAll(index, c);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean removeAll(Collection<?> c) {
        return list.removeAll(c);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean retainAll(Collection<?> c) {
        return list.retainAll(c);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void replaceAll(UnaryOperator<TopLevelElement> operator) {
        list.replaceAll(operator);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void sort(Comparator<? super TopLevelElement> c) {
        list.sort(c);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void clear() {
        list.clear();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TopLevelElement get(int index) {
        return list.get(index);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TopLevelElement set(int index, TopLevelElement element) {
        return list.set(index, element);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void add(int index, TopLevelElement element) {
        list.add(index, element);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public TopLevelElement remove(int index) {
        return list.remove(index);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int indexOf(Object o) {
        return list.indexOf(o);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int lastIndexOf(Object o) {
        return list.lastIndexOf(o);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ListIterator<TopLevelElement> listIterator() {
        return list.listIterator();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public ListIterator<TopLevelElement> listIterator(int index) {
        return list.listIterator(index);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public List<TopLevelElement> subList(int fromIndex, int toIndex) {
        return list.subList(fromIndex, toIndex);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Spliterator<TopLevelElement> spliterator() {
        return list.spliterator();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean removeIf(Predicate<? super TopLevelElement> filter) {
        return list.removeIf(filter);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Stream<TopLevelElement> stream() {
        return list.stream();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public Stream<TopLevelElement> parallelStream() {
        return list.parallelStream();
    }

}

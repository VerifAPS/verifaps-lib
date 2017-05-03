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
import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * Created by weigl on 11.06.14.
 *
 * @author weigl
 * @version $Id: $Id
 */
public class ExpressionList extends Expression
        implements List<Expression> {
    private List<Expression> expressions = new ArrayList<>();

    /** {@inheritDoc} */
    @Override
    public int size() {
        return expressions.size();
    }

    /** {@inheritDoc} */
    @Override
    public boolean isEmpty() {
        return expressions.isEmpty();
    }

    /** {@inheritDoc} */
    @Override
    public boolean contains(Object o) {
        return expressions.contains(o);
    }

    /** {@inheritDoc} */
    @Override
    public Iterator<Expression> iterator() {
        return expressions.iterator();
    }

    /** {@inheritDoc} */
    @Override
    public Object[] toArray() {
        return expressions.toArray();
    }

    /** {@inheritDoc} */
    @Override
    public <T> T[] toArray(T[] a) {
        return expressions.toArray(a);
    }

    /** {@inheritDoc} */
    @Override
    public boolean add(Expression expression) {
        return expressions.add(expression);
    }

    /** {@inheritDoc} */
    @Override
    public boolean remove(Object o) {
        return expressions.remove(o);
    }

    /** {@inheritDoc} */
    @Override
    public boolean containsAll(Collection<?> c) {
        return expressions.containsAll(c);
    }

    /** {@inheritDoc} */
    @Override
    public boolean addAll(Collection<? extends Expression> c) {
        return expressions.addAll(c);
    }

    /** {@inheritDoc} */
    @Override
    public boolean addAll(int index, Collection<? extends Expression> c) {
        return expressions.addAll(index, c);
    }

    /** {@inheritDoc} */
    @Override
    public boolean removeAll(Collection<?> c) {
        return expressions.removeAll(c);
    }

    /** {@inheritDoc} */
    @Override
    public boolean retainAll(Collection<?> c) {
        return expressions.retainAll(c);
    }

    /** {@inheritDoc} */
    @Override
    public void replaceAll(UnaryOperator<Expression> operator) {
        expressions.replaceAll(operator);
    }

    /** {@inheritDoc} */
    @Override
    public void sort(Comparator<? super Expression> c) {
        expressions.sort(c);
    }

    /** {@inheritDoc} */
    @Override
    public void clear() {
        expressions.clear();
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object o) {
        return expressions.equals(o);
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return expressions.hashCode();
    }

    /** {@inheritDoc} */
    @Override
    public Expression get(int index) {
        return expressions.get(index);
    }

    /** {@inheritDoc} */
    @Override
    public Expression set(int index, Expression element) {
        return expressions.set(index, element);
    }

    /** {@inheritDoc} */
    @Override
    public void add(int index, Expression element) {
        expressions.add(index, element);
    }

    /** {@inheritDoc} */
    @Override
    public Expression remove(int index) {
        return expressions.remove(index);
    }

    /** {@inheritDoc} */
    @Override
    public int indexOf(Object o) {
        return expressions.indexOf(o);
    }

    /** {@inheritDoc} */
    @Override
    public int lastIndexOf(Object o) {
        return expressions.lastIndexOf(o);
    }

    /** {@inheritDoc} */
    @Override
    public ListIterator<Expression> listIterator() {
        return expressions.listIterator();
    }

    /** {@inheritDoc} */
    @Override
    public ListIterator<Expression> listIterator(int index) {
        return expressions.listIterator(index);
    }

    /** {@inheritDoc} */
    @Override
    public List<Expression> subList(int fromIndex, int toIndex) {
        return expressions.subList(fromIndex, toIndex);
    }

    /** {@inheritDoc} */
    @Override
    public Spliterator<Expression> spliterator() {
        return expressions.spliterator();
    }

    /** {@inheritDoc} */
    @Override
    public boolean removeIf(Predicate<? super Expression> filter) {
        return expressions.removeIf(filter);
    }

    /** {@inheritDoc} */
    @Override
    public Stream<Expression> stream() {
        return expressions.stream();
    }

    /** {@inheritDoc} */
    @Override
    public Stream<Expression> parallelStream() {
        return expressions.parallelStream();
    }

    /** {@inheritDoc} */
    @Override
    public void forEach(Consumer<? super Expression> action) {
        expressions.forEach(action);
    }

    /** {@inheritDoc} */
    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /** {@inheritDoc} */
    @Override
    public Any dataType(LocalScope localScope) {
        throw new IllegalStateException("not implemented");
    }

    @Override public ExpressionList clone() {
        ExpressionList el = new ExpressionList();
        forEach(e -> el.add(e.clone()));
        return el;
    }
}

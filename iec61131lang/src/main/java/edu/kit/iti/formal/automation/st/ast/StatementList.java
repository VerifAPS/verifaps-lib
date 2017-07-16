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

import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.visitors.Visitor;
import lombok.EqualsAndHashCode;
import lombok.ToString;
import org.intellij.lang.annotations.Flow;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * Created by weigla on 09.06.2014.
 *
 * @author weigl
 * @version $Id: $Id
 */
@EqualsAndHashCode
@ToString
public class StatementList
        implements List<Statement>, Copyable<StatementList>, Visitable {
    private List<Statement> list = new ArrayList<>();

    public StatementList() {
    }

    public StatementList(Statement... then) {
        list = new ArrayList<>(Arrays.asList(then));
    }

    public StatementList(StatementList statements) {
        addAll(statements);
    }

    public StatementList(Collection<Statement> ts) {
        list = new ArrayList<>(ts);
    }

    /**
     * {@inheritDoc}
     */
    public <T> T accept(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean add(Statement statement) {
        if (statement == null) {
            throw new IllegalArgumentException("null added");
        }
        return list.add(statement);
    }

    @Override
    public boolean remove(Object o) {
        return list.remove(o);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return list.containsAll(c);
    }

    @Override
    public boolean addAll(@Flow(sourceIsContainer = true, targetIsContainer = true) Collection<? extends Statement> c) {
        return list.addAll(c);
    }

    @Override
    public boolean addAll(int index, @Flow(sourceIsContainer = true, targetIsContainer = true) Collection<? extends Statement> c) {
        return list.addAll(index, c);
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        return list.removeAll(c);
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        return list.retainAll(c);
    }

    @Override
    public void replaceAll(UnaryOperator<Statement> operator) {
        list.replaceAll(operator);
    }

    @Override
    public void sort(Comparator<? super Statement> c) {
        list.sort(c);
    }

    @Override
    public void clear() {
        list.clear();
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public void add(int index, Statement element) {
        if (element == null) {
            System.err.println("null added");
            return;
        }

        list.add(index, element);
    }

    @Override
    public Statement remove(int index) {
        return list.remove(index);
    }

    @Override
    public int indexOf(Object o) {
        return list.indexOf(o);
    }

    @Override
    public int lastIndexOf(Object o) {
        return list.lastIndexOf(o);
    }

    @Override
    public ListIterator<Statement> listIterator() {
        return list.listIterator();
    }

    @Override
    public ListIterator<Statement> listIterator(int index) {
        return list.listIterator(index);
    }

    @Override
    public List<Statement> subList(int fromIndex, int toIndex) {
        return list.subList(fromIndex, toIndex);
    }

    @Override
    public Spliterator<Statement> spliterator() {
        return list.spliterator();
    }

    @Override
    public boolean removeIf(Predicate<? super Statement> filter) {
        return list.removeIf(filter);
    }

    @Override
    public Stream<Statement> stream() {
        return list.stream();
    }

    @Override
    public Stream<Statement> parallelStream() {
        return list.parallelStream();
    }

    @Override
    public void forEach(Consumer<? super Statement> action) {
        list.forEach(action);
    }

    public void comment(String format, Object... args) {
        add(new CommentStatement(format, args));
    }

    @Override
    public StatementList copy() {
        StatementList sl = new StatementList();
        forEach(s -> sl.add(s.copy()));
        return sl;
    }

    @Override
    public int size() {
        return list.size();
    }

    @Override
    public boolean isEmpty() {
        return list.isEmpty();
    }

    @Override
    public boolean contains(Object o) {
        return list.contains(o);
    }

    @Override
    public Iterator<Statement> iterator() {
        return list.iterator();
    }

    @Override
    public Object[] toArray() {
        return list.toArray();
    }

    @Override
    public <T> T[] toArray(T[] a) {
        return list.toArray(a);
    }


    @Override
    public Statement get(int index) {
        return list.get(index);
    }

    @Override
    public Statement set(int index, @Flow(targetIsContainer = true) Statement element) {
        return list.set(index, element);
    }
}

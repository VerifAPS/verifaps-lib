package edu.kit.iti.formal.automation.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * Created by weigl on 11.06.14.
 */
public class ExpressionList extends Expression implements List<Expression> {
    private List<Expression> expressions = new ArrayList<>();

    @Override
    public int size() {
        return expressions.size();
    }

    @Override
    public boolean isEmpty() {
        return expressions.isEmpty();
    }

    @Override
    public boolean contains(Object o) {
        return expressions.contains(o);
    }

    @Override
    public Iterator<Expression> iterator() {
        return expressions.iterator();
    }

    @Override
    public Object[] toArray() {
        return expressions.toArray();
    }

    @Override
    public <T> T[] toArray(T[] a) {
        return expressions.toArray(a);
    }

    @Override
    public boolean add(Expression expression) {
        return expressions.add(expression);
    }

    @Override
    public boolean remove(Object o) {
        return expressions.remove(o);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return expressions.containsAll(c);
    }

    @Override
    public boolean addAll(Collection<? extends Expression> c) {
        return expressions.addAll(c);
    }

    @Override
    public boolean addAll(int index, Collection<? extends Expression> c) {
        return expressions.addAll(index, c);
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        return expressions.removeAll(c);
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        return expressions.retainAll(c);
    }

    @Override
    public void replaceAll(UnaryOperator<Expression> operator) {
        expressions.replaceAll(operator);
    }

    @Override
    public void sort(Comparator<? super Expression> c) {
        expressions.sort(c);
    }

    @Override
    public void clear() {
        expressions.clear();
    }

    @Override
    public boolean equals(Object o) {
        return expressions.equals(o);
    }

    @Override
    public int hashCode() {
        return expressions.hashCode();
    }

    @Override
    public Expression get(int index) {
        return expressions.get(index);
    }

    @Override
    public Expression set(int index, Expression element) {
        return expressions.set(index, element);
    }

    @Override
    public void add(int index, Expression element) {
        expressions.add(index, element);
    }

    @Override
    public Expression remove(int index) {
        return expressions.remove(index);
    }

    @Override
    public int indexOf(Object o) {
        return expressions.indexOf(o);
    }

    @Override
    public int lastIndexOf(Object o) {
        return expressions.lastIndexOf(o);
    }

    @Override
    public ListIterator<Expression> listIterator() {
        return expressions.listIterator();
    }

    @Override
    public ListIterator<Expression> listIterator(int index) {
        return expressions.listIterator(index);
    }

    @Override
    public List<Expression> subList(int fromIndex, int toIndex) {
        return expressions.subList(fromIndex, toIndex);
    }

    @Override
    public Spliterator<Expression> spliterator() {
        return expressions.spliterator();
    }

    @Override
    public boolean removeIf(Predicate<? super Expression> filter) {
        return expressions.removeIf(filter);
    }

    @Override
    public Stream<Expression> stream() {
        return expressions.stream();
    }

    @Override
    public Stream<Expression> parallelStream() {
        return expressions.parallelStream();
    }

    @Override
    public void forEach(Consumer<? super Expression> action) {
        expressions.forEach(action);
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }
}

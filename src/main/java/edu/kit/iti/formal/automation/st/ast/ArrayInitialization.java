package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.LocalScope;
import edu.kit.iti.formal.automation.datatypes.Any;
import edu.kit.iti.formal.automation.exceptions.TypeConformityException;
import edu.kit.iti.formal.automation.exceptions.VariableNotDefinedinScope;
import edu.kit.iti.formal.automation.visitors.Visitable;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * Created by weigl on 13.06.14.
 */
public class ArrayInitialization<T> extends Initialization
        implements List<Initialization>, Visitable {
    private List<Initialization> initValues = new ArrayList<>();


    @Override
    public boolean add(Initialization initialization) {
        return initValues.add(initialization);
    }

    @Override
    public boolean remove(Object o) {
        return initValues.remove(o);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return initValues.containsAll(c);
    }

    @Override
    public boolean addAll(Collection<? extends Initialization> c) {
        return initValues.addAll(c);
    }

    @Override
    public boolean addAll(int index, Collection<? extends Initialization> c) {
        return initValues.addAll(index, c);
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        return initValues.removeAll(c);
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        return initValues.retainAll(c);
    }

    @Override
    public void replaceAll(UnaryOperator<Initialization> operator) {
        initValues.replaceAll(operator);
    }

    @Override
    public void sort(Comparator<? super Initialization> c) {
        initValues.sort(c);
    }

    @Override
    public void clear() {
        initValues.clear();
    }

    @Override
    public boolean equals(Object o) {
        return initValues.equals(o);
    }

    @Override
    public int hashCode() {
        return initValues.hashCode();
    }

    @Override
    public Initialization get(int index) {
        return initValues.get(index);
    }

    @Override
    public Initialization set(int index, Initialization element) {
        return initValues.set(index, element);
    }

    @Override
    public void add(int index, Initialization element) {
        initValues.add(index, element);
    }

    @Override
    public Initialization remove(int index) {
        return initValues.remove(index);
    }

    @Override
    public int indexOf(Object o) {
        return initValues.indexOf(o);
    }

    @Override
    public int lastIndexOf(Object o) {
        return initValues.lastIndexOf(o);
    }

    @Override
    public ListIterator<Initialization> listIterator() {
        return initValues.listIterator();
    }

    @Override
    public ListIterator<Initialization> listIterator(int index) {
        return initValues.listIterator(index);
    }

    @Override
    public List<Initialization> subList(int fromIndex, int toIndex) {
        return initValues.subList(fromIndex, toIndex);
    }

    @Override
    public Spliterator<Initialization> spliterator() {
        return initValues.spliterator();
    }

    @Override
    public boolean removeIf(Predicate<? super Initialization> filter) {
        return initValues.removeIf(filter);
    }

    @Override
    public Stream<Initialization> stream() {
        return initValues.stream();
    }

    @Override
    public Stream<Initialization> parallelStream() {
        return initValues.parallelStream();
    }

    @Override
    public void forEach(Consumer<? super Initialization> action) {
        initValues.forEach(action);
    }

    @Override
    public int size() {
        return initValues.size();
    }

    @Override
    public boolean isEmpty() {
        return initValues.isEmpty();
    }

    @Override
    public boolean contains(Object o) {
        return initValues.contains(o);
    }

    @Override
    public Iterator<Initialization> iterator() {
        return initValues.iterator();
    }

    @Override
    public Object[] toArray() {
        return initValues.toArray();
    }

    @Override
    public <T> T[] toArray(T[] a) {
        return initValues.toArray(a);
    }

    @Override
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public Any dataType(LocalScope localScope)
            throws VariableNotDefinedinScope, TypeConformityException {
        //TODO
        return null;
    }
}

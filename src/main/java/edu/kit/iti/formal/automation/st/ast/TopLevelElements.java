package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.scope.LocalScope;
import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.*;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * @author weigla
 * @date 04.07.2014
 */
public class TopLevelElements extends Top implements List<TopLevelElement> {
    //private LocalScope commonScore = new LocalScope();
    private List<TopLevelElement> list = new ArrayList<>();

    public TopLevelElements() {
    }

    public TopLevelElements(List<TopLevelElement> elements) {
        list = new ArrayList<>(elements);
    }

    public <T> T visit(Visitor<T> sev) {//empty
        list.stream().forEach(a->a.visit(sev));
        return null;
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
    public Iterator<TopLevelElement> iterator() {
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
    public boolean add(TopLevelElement topLevelElement) {
        return list.add(topLevelElement);
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
    public boolean addAll(Collection<? extends TopLevelElement> c) {
        return list.addAll(c);
    }

    @Override
    public boolean addAll(int index, Collection<? extends TopLevelElement> c) {
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
    public void replaceAll(UnaryOperator<TopLevelElement> operator) {
        list.replaceAll(operator);
    }

    @Override
    public void sort(Comparator<? super TopLevelElement> c) {
        list.sort(c);
    }

    @Override
    public void clear() {
        list.clear();
    }

    @Override
    public boolean equals(Object o) {
        return list.equals(o);
    }

    @Override
    public int hashCode() {
        return list.hashCode();
    }

    @Override
    public TopLevelElement get(int index) {
        return list.get(index);
    }

    @Override
    public TopLevelElement set(int index, TopLevelElement element) {
        return list.set(index, element);
    }

    @Override
    public void add(int index, TopLevelElement element) {
        list.add(index, element);
    }

    @Override
    public TopLevelElement remove(int index) {
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
    public ListIterator<TopLevelElement> listIterator() {
        return list.listIterator();
    }

    @Override
    public ListIterator<TopLevelElement> listIterator(int index) {
        return list.listIterator(index);
    }

    @Override
    public List<TopLevelElement> subList(int fromIndex, int toIndex) {
        return list.subList(fromIndex, toIndex);
    }

    @Override
    public Spliterator<TopLevelElement> spliterator() {
        return list.spliterator();
    }

    @Override
    public boolean removeIf(Predicate<? super TopLevelElement> filter) {
        return list.removeIf(filter);
    }

    @Override
    public Stream<TopLevelElement> stream() {
        return list.stream();
    }

    @Override
    public Stream<TopLevelElement> parallelStream() {
        return list.parallelStream();
    }
}

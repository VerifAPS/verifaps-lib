package edu.kit.iti.formal.automation.st.ast;

import edu.kit.iti.formal.automation.visitors.Visitor;

import java.util.*;
import java.util.function.Consumer;
import java.util.function.Predicate;
import java.util.function.UnaryOperator;
import java.util.stream.Stream;

/**
 * Created by weigl on 13.06.14.
 */
public class TypeDeclarations extends TopLevelElement implements List<TypeDeclaration> {
    private List<TypeDeclaration> declarations = new ArrayList<>();

    public TypeDeclarations() {
    }

    public TypeDeclarations(TypeDeclaration... stp) {
        super();

        declarations.addAll(Arrays.asList(stp));
    }

    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override
    public int size() {
        return declarations.size();
    }

    @Override
    public boolean isEmpty() {
        return declarations.isEmpty();
    }

    @Override
    public boolean contains(Object o) {
        return declarations.contains(o);
    }

    @Override
    public Iterator<TypeDeclaration> iterator() {
        return declarations.iterator();
    }

    @Override
    public Object[] toArray() {
        return declarations.toArray();
    }

    @Override
    public <T> T[] toArray(T[] a) {
        return declarations.toArray(a);
    }

    @Override
    public boolean add(TypeDeclaration typeDeclaration) {
        return declarations.add(typeDeclaration);
    }

    @Override
    public boolean remove(Object o) {
        return declarations.remove(o);
    }

    @Override
    public boolean containsAll(Collection<?> c) {
        return declarations.containsAll(c);
    }

    @Override
    public boolean addAll(Collection<? extends TypeDeclaration> c) {
        return declarations.addAll(c);
    }

    @Override
    public boolean addAll(int index, Collection<? extends TypeDeclaration> c) {
        return declarations.addAll(index, c);
    }

    @Override
    public boolean removeAll(Collection<?> c) {
        return declarations.removeAll(c);
    }

    @Override
    public boolean retainAll(Collection<?> c) {
        return declarations.retainAll(c);
    }

    @Override
    public void replaceAll(UnaryOperator<TypeDeclaration> operator) {
        declarations.replaceAll(operator);
    }

    @Override
    public void sort(Comparator<? super TypeDeclaration> c) {
        declarations.sort(c);
    }

    @Override
    public void clear() {
        declarations.clear();
    }

    @Override
    public boolean equals(Object o) {
        return declarations.equals(o);
    }

    @Override
    public int hashCode() {
        return declarations.hashCode();
    }

    @Override
    public TypeDeclaration get(int index) {
        return declarations.get(index);
    }

    @Override
    public TypeDeclaration set(int index, TypeDeclaration element) {
        return declarations.set(index, element);
    }

    @Override
    public void add(int index, TypeDeclaration element) {
        declarations.add(index, element);
    }

    @Override
    public TypeDeclaration remove(int index) {
        return declarations.remove(index);
    }

    @Override
    public int indexOf(Object o) {
        return declarations.indexOf(o);
    }

    @Override
    public int lastIndexOf(Object o) {
        return declarations.lastIndexOf(o);
    }

    @Override
    public ListIterator<TypeDeclaration> listIterator() {
        return declarations.listIterator();
    }

    @Override
    public ListIterator<TypeDeclaration> listIterator(int index) {
        return declarations.listIterator(index);
    }

    @Override
    public List<TypeDeclaration> subList(int fromIndex, int toIndex) {
        return declarations.subList(fromIndex, toIndex);
    }

    @Override
    public Spliterator<TypeDeclaration> spliterator() {
        return declarations.spliterator();
    }

    @Override
    public boolean removeIf(Predicate<? super TypeDeclaration> filter) {
        return declarations.removeIf(filter);
    }

    @Override
    public Stream<TypeDeclaration> stream() {
        return declarations.stream();
    }

    @Override
    public Stream<TypeDeclaration> parallelStream() {
        return declarations.parallelStream();
    }

    @Override
    public void forEach(Consumer<? super TypeDeclaration> action) {
        declarations.forEach(action);
    }

    public boolean declares(String typeName) {
        for (TypeDeclaration td : this) {
            if (td.getTypeName().equals(typeName))
                return true;
        }
        return false;
    }

    @Override
    public String getBlockName() {
        return "types";
    }
}

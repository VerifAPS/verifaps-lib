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
public class TypeDeclarations extends TopLevelElement implements List<TypeDeclaration> {
    private List<TypeDeclaration> declarations = new ArrayList<>();

    /**
     * <p>Constructor for TypeDeclarations.</p>
     */
    public TypeDeclarations() {
    }

    /**
     * <p>Constructor for TypeDeclarations.</p>
     *
     * @param stp a {@link edu.kit.iti.formal.automation.st.ast.TypeDeclaration} object.
     */
    public TypeDeclarations(TypeDeclaration... stp) {
        super();

        declarations.addAll(Arrays.asList(stp));
    }

    /** {@inheritDoc} */
    public <T> T visit(Visitor<T> visitor) {
        return visitor.visit(this);
    }

    @Override public TypeDeclarations clone() {
        TypeDeclarations td = new TypeDeclarations();
        forEach(t -> td.add(t.clone()));
        return td;
    }

    /** {@inheritDoc} */
    @Override
    public int size() {
        return declarations.size();
    }

    /** {@inheritDoc} */
    @Override
    public boolean isEmpty() {
        return declarations.isEmpty();
    }

    /** {@inheritDoc} */
    @Override
    public boolean contains(Object o) {
        return declarations.contains(o);
    }

    /** {@inheritDoc} */
    @Override
    public Iterator<TypeDeclaration> iterator() {
        return declarations.iterator();
    }

    /** {@inheritDoc} */
    @Override
    public Object[] toArray() {
        return declarations.toArray();
    }

    /** {@inheritDoc} */
    @Override
    public <T> T[] toArray(T[] a) {
        return declarations.toArray(a);
    }

    /** {@inheritDoc} */
    @Override
    public boolean add(TypeDeclaration typeDeclaration) {
        return declarations.add(typeDeclaration);
    }

    /** {@inheritDoc} */
    @Override
    public boolean remove(Object o) {
        return declarations.remove(o);
    }

    /** {@inheritDoc} */
    @Override
    public boolean containsAll(Collection<?> c) {
        return declarations.containsAll(c);
    }

    /** {@inheritDoc} */
    @Override
    public boolean addAll(Collection<? extends TypeDeclaration> c) {
        return declarations.addAll(c);
    }

    /** {@inheritDoc} */
    @Override
    public boolean addAll(int index, Collection<? extends TypeDeclaration> c) {
        return declarations.addAll(index, c);
    }

    /** {@inheritDoc} */
    @Override
    public boolean removeAll(Collection<?> c) {
        return declarations.removeAll(c);
    }

    /** {@inheritDoc} */
    @Override
    public boolean retainAll(Collection<?> c) {
        return declarations.retainAll(c);
    }

    /** {@inheritDoc} */
    @Override
    public void replaceAll(UnaryOperator<TypeDeclaration> operator) {
        declarations.replaceAll(operator);
    }

    /** {@inheritDoc} */
    @Override
    public void sort(Comparator<? super TypeDeclaration> c) {
        declarations.sort(c);
    }

    /** {@inheritDoc} */
    @Override
    public void clear() {
        declarations.clear();
    }

    /** {@inheritDoc} */
    @Override
    public boolean equals(Object o) {
        return declarations.equals(o);
    }

    /** {@inheritDoc} */
    @Override
    public int hashCode() {
        return declarations.hashCode();
    }

    /** {@inheritDoc} */
    @Override
    public TypeDeclaration get(int index) {
        return declarations.get(index);
    }

    /** {@inheritDoc} */
    @Override
    public TypeDeclaration set(int index, TypeDeclaration element) {
        return declarations.set(index, element);
    }

    /** {@inheritDoc} */
    @Override
    public void add(int index, TypeDeclaration element) {
        declarations.add(index, element);
    }

    /** {@inheritDoc} */
    @Override
    public TypeDeclaration remove(int index) {
        return declarations.remove(index);
    }

    /** {@inheritDoc} */
    @Override
    public int indexOf(Object o) {
        return declarations.indexOf(o);
    }

    /** {@inheritDoc} */
    @Override
    public int lastIndexOf(Object o) {
        return declarations.lastIndexOf(o);
    }

    /** {@inheritDoc} */
    @Override
    public ListIterator<TypeDeclaration> listIterator() {
        return declarations.listIterator();
    }

    /** {@inheritDoc} */
    @Override
    public ListIterator<TypeDeclaration> listIterator(int index) {
        return declarations.listIterator(index);
    }

    /** {@inheritDoc} */
    @Override
    public List<TypeDeclaration> subList(int fromIndex, int toIndex) {
        return declarations.subList(fromIndex, toIndex);
    }

    /** {@inheritDoc} */
    @Override
    public Spliterator<TypeDeclaration> spliterator() {
        return declarations.spliterator();
    }

    /** {@inheritDoc} */
    @Override
    public boolean removeIf(Predicate<? super TypeDeclaration> filter) {
        return declarations.removeIf(filter);
    }

    /** {@inheritDoc} */
    @Override
    public Stream<TypeDeclaration> stream() {
        return declarations.stream();
    }

    /** {@inheritDoc} */
    @Override
    public Stream<TypeDeclaration> parallelStream() {
        return declarations.parallelStream();
    }

    /** {@inheritDoc} */
    @Override
    public void forEach(Consumer<? super TypeDeclaration> action) {
        declarations.forEach(action);
    }

    /**
     * <p>declares.</p>
     *
     * @param typeName a {@link java.lang.String} object.
     * @return a boolean.
     */
    public boolean declares(String typeName) {
        for (TypeDeclaration td : this) {
            if (td.getTypeName().equals(typeName))
                return true;
        }
        return false;
    }

    /** {@inheritDoc} */
    @Override public String getIdentifier() {
        return "types";
    }
}

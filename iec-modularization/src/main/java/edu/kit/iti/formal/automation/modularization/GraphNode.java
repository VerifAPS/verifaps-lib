package edu.kit.iti.formal.automation.modularization;

/*-
 * #%L
 * iec-modularization
 * %%
 * Copyright (C) 2017 Alexander Weigl
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
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import java.util.*;

public final class GraphNode<T> {

	private static final class Counter {
		int _value = 0;
	}

	private final class ElementIterator implements Iterator<T> {

		private Iterator<GraphNode<T>> _it;

		private ElementIterator(Iterable<GraphNode<T>> source) {
			_it = source.iterator();
		}

		@Override
		public final boolean hasNext() {
			return _it.hasNext();
		}

		@Override
		public final T next() {
			return _it.next().element;
		}
	}

	public T element = null;

	public final Set<GraphNode<T>> pred = new HashSet<>();
	public final Set<GraphNode<T>> succ = new HashSet<>();

	public final Iterable<T> predElements = () -> new ElementIterator(pred);
	public final Iterable<T> succElements = () -> new ElementIterator(succ);

	public GraphNode() {}

	public GraphNode(final T element) {
		this.element = element;
	}

	public final void addPredecessor(final GraphNode<T> node) {
		pred     .add(node);
		node.succ.add(this);
	}

	public final void addPredecessors(final Iterable<GraphNode<T>> nodes) {
		for(GraphNode<T> i : nodes) addPredecessor(i);
	}

	public final void addSuccessor(final GraphNode<T> node) {
		succ     .add(node);
		node.pred.add(this);
	}

	public final void addSuccessors(final Iterable<GraphNode<T>> nodes) {
		for(GraphNode<T> i : nodes) addSuccessor(i);
	}

	public static <T> List<GraphNode<T>> orderNodes(
			final Collection<GraphNode<T>> nodes) {

		final Map<GraphNode<T>, Counter> predCounters = new HashMap<>();

		final List<GraphNode<T>> ordered    = new ArrayList<>(nodes.size());
		final Set <GraphNode<T>> notChecked = new HashSet<>(nodes);

		for(GraphNode<T> i : nodes) predCounters.put(i, new Counter());

		while(!notChecked.isEmpty()) {

			GraphNode<T> nextNode = null;

			for(GraphNode<T> i : notChecked) {
				if(predCounters.get(i)._value == i.pred.size()) {
					nextNode = i;
					break;
				}
			}

			// Ensure graph consistency
			assert nextNode != null;

			ordered   .add   (nextNode);
			notChecked.remove(nextNode);

			// Increase the counter of all successor nodes
			for(GraphNode<T> j : nextNode.succ) predCounters.get(j)._value++;
		}

		return ordered;
	}
}

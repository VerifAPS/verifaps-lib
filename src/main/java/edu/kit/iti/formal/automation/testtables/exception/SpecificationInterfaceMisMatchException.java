/*
 * geteta
 *
 * Copyright (C) 2016-2018 -- Alexander Weigl <weigl@kit.edu>
 *
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
 */
package edu.kit.iti.formal.automation.testtables.exception;


import com.google.common.collect.Streams;
import edu.kit.iti.formal.smv.ast.SMVModule;
import edu.kit.iti.formal.smv.ast.SVariable;

import java.util.*;
import java.util.stream.Collectors;

/**
 * @author Alexander Weigl
 * @version 1 (13.12.16)
 */
public class SpecificationInterfaceMisMatchException extends GetetaException {
    public SpecificationInterfaceMisMatchException() {
        super();
    }

    public SpecificationInterfaceMisMatchException(String message) {
        super(message);
    }

    public SpecificationInterfaceMisMatchException(String message, Throwable cause) {
        super(message, cause);
    }

    public SpecificationInterfaceMisMatchException(Throwable cause) {
        super(cause);
    }

    protected SpecificationInterfaceMisMatchException(String message, Throwable cause,
                                                      boolean enableSuppression,
                                                      boolean writableStackTrace) {
        super(message, cause, enableSuppression, writableStackTrace);
    }

    public SpecificationInterfaceMisMatchException(SMVModule code, SVariable v) {
        super(String.format("Could not find variable '%s' in module: %s. Candidates would be: %s", v.getName(), code.getName(),
                candidates(v.getName(), code)
        ));
    }

    private static String candidates(String name, SMVModule code) {
        List<String> candidates =
                Streams.concat(code.getStateVars().stream(),
                        Streams.concat(code.getInputVars().stream(), code.getFrozenVars().stream()))
                        .map(SVariable::getName)
                        .collect(Collectors.toList());
        Collection<String> best = candidates(name, candidates);
        return best.stream().limit(3).collect(Collectors.joining(", ","[","]"));
    }

    private static Collection<String> candidates(String name, List<String> code) {
        PriorityQueue<String> heap = new PriorityQueue<>(
                new LevensteinCaseInsensitiveComparator(name));
        heap.addAll(code);
        return heap;
    }

    static class LevensteinCaseInsensitiveComparator implements Comparator<String> {
        private final String reference;
        public Map<String, Integer> computed = new HashMap<>();

        public LevensteinCaseInsensitiveComparator(String name) {
            this.reference = name.toLowerCase();
        }


        @Override
        public int compare(String o1, String o2) {
            int level1 = getLevenstheinToRef(o1);
            int level2 = getLevenstheinToRef(o2);
            return Integer.compare(level1, level2);
        }

        private int getLevenstheinToRef(String o1) {
            String k = o1.toLowerCase();
            return computed.computeIfAbsent(k, s -> levenshteinDistance(reference, s));
        }

        /**
         * from https://en.wikibooks.org/wiki/Algorithm_Implementation/Strings/Levenshtein_distance#Java
         *
         * @param lhs
         * @param rhs
         * @return
         */
        public int levenshteinDistance(CharSequence lhs, CharSequence rhs) {
            int len0 = lhs.length() + 1;
            int len1 = rhs.length() + 1;

            // the array of distances
            int[] cost = new int[len0];
            int[] newcost = new int[len0];

            // initial cost of skipping prefix in String s0
            for (int i = 0; i < len0; i++) cost[i] = i;

            // dynamically computing the array of distances

            // transformation cost for each letter in s1
            for (int j = 1; j < len1; j++) {
                // initial cost of skipping prefix in String s1
                newcost[0] = j;

                // transformation cost for each letter in s0
                for (int i = 1; i < len0; i++) {
                    // matching current letters in both strings
                    int match = (lhs.charAt(i - 1) == rhs.charAt(j - 1)) ? 0 : 1;

                    // computing cost for each transformation
                    int cost_replace = cost[i - 1] + match;
                    int cost_insert = cost[i] + 1;
                    int cost_delete = newcost[i - 1] + 1;

                    // keep minimum cost
                    newcost[i] = Math.min(Math.min(cost_insert, cost_delete), cost_replace);
                }

                // swap cost/newcost arrays
                int[] swap = cost;
                cost = newcost;
                newcost = swap;
            }

            // the distance is the cost for transforming all letters in both strings
            return cost[len0 - 1];
        }
    }
}

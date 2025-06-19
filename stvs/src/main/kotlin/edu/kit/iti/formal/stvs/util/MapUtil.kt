/* *****************************************************************
 * This file belongs to verifaps-lib (https://verifaps.github.io).
 * SPDX-License-Header: GPL-3.0-or-later
 * 
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * *****************************************************************/
package edu.kit.iti.formal.stvs.util

import java.util.function.BiFunction
import java.util.function.Function

/**
 * Util class for map functions.
 *
 * @author Philipp
 */
object MapUtil {
    /**
     * Applies [MapUtil.mapValuesWithKey] with an empty target
     * map and ignores indices of source elements.
     *
     * @param sourceMap map to operate on.
     * @param mapper Function that maps from `sourceMap`
     * elements to `mapToAddTo` elements.
     * @param <K> index type of both maps
     * @param <V0> value type of source map
     * @param <V1> value type of target map
     * @see MapUtil.mapValuesWithKey
     * @return map with mapped values
     </V1></V0></K> */
    fun <K, V0, V1> mapValues(sourceMap: Map<K, V0>, mapper: Function<V0, V1>): Map<K, V1> =
        mapValuesWithKey(sourceMap) { key: K, value: V0 -> mapper.apply(value) }

    /**
     * Applies [MapUtil.mapValuesWithKey] with an empty target map.
     *
     * @param sourceMap map to operate on.
     * @param mapper Function that maps from `sourceMap`
     * elements and their index to `mapToAddTo` elements.
     * @param <K> index type of both maps
     * @param <V0> value type of source map
     * @param <V1> value type of target map
     * @see MapUtil.mapValuesWithKey
     * @return map with mapped values
     </V1></V0></K> */
    fun <K, V0, V1> mapValuesWithKey(sourceMap: Map<K, V0>, mapper: BiFunction<K, V0, V1>): Map<K, V1> {
        val map: MutableMap<K, V1> = HashMap()
        mapValuesWithKey(sourceMap, map, mapper)
        return map
    }

    /**
     * Takes each element of `sourceMap` and calls `mapper`
     * with the index and value of the element.
     * The returned value is added to `mapToAddTo`.
     *
     * @param sourceMap map to operate on.
     * @param mapToAddTo Target map. Mapped elements will be put in this map.
     * @param mapper Function that maps from `sourceMap`
     * elements and their index to `mapToAddTo` elements.
     * @param <K> index type of both maps
     * @param <V0> value type of source map
     * @param <V1> value type of target map
     </V1></V0></K> */
    fun <K, V0, V1> mapValuesWithKey(
        sourceMap: Map<K, V0>,
        mapToAddTo: MutableMap<K, V1>,
        mapper: BiFunction<K, V0, V1>,
    ) {
        for ((key, value) in sourceMap) {
            mapToAddTo[key] = mapper.apply(key, value)
        }
    }
}
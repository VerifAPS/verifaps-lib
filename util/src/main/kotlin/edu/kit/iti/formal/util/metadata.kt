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
package edu.kit.iti.formal.util

/**
 * This interface signals, that a class/object supports additional user-defined metadata.
 *
 * @author Alexander Weigl
 * @version 1 (28.06.19)
 */
interface HasMetadata {
    fun metadata(create: Boolean = false): Metadata?
    fun ensureMetadata() = metadata(true)!!

    fun copyMetaFrom(m: HasMetadata) {
        m.metadata()?.let {
            ensureMetadata().copyFrom(it)
        }
    }
}

inline fun <reified T : Any?> HasMetadata.meta() = metadata()?.get(T::class.java)

inline fun <reified T : Any?> HasMetadata.meta(obj: T) {
    val c = T::class.java
    ensureMetadata().set(c, obj)
}

class HasMetadataImpl : HasMetadata {
    private var _metadata: Metadata? = null
    override fun metadata(create: Boolean): Metadata? {
        if (create && _metadata == null) {
            _metadata = Metadata()
        }
        return _metadata
    }
}

class Metadata {
    private var metadata: HashMap<String, Any>? = null

    fun <T> get(clazz: Class<T>): T? = get(clazz.name)

    @Suppress("UNCHECKED_CAST")
    fun <T> get(key: String): T? = metadata?.get(key) as T?
    fun <T : Any?> set(clazz: Class<T>, obj: T) = set(clazz.name, obj)
    fun <T : Any?> set(key: String, obj: T) {
        if (obj == null) {
            metadata?.remove(key)
        } else {
            if (metadata == null) {
                metadata = HashMap()
            }
            metadata?.put(key, obj)
        }
    }

    fun copyFrom(other: Metadata) {
        if (!other.metadata.isNullOrEmpty()) {
            metadata = HashMap(other.metadata)
        }
    }
}
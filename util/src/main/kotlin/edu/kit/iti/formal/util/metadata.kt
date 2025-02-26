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
        if (create && _metadata == null)
            _metadata = Metadata()
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
        if (!other.metadata.isNullOrEmpty())
            metadata = HashMap(other.metadata)
    }
}

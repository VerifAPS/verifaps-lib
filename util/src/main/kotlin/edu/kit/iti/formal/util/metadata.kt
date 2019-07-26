package edu.kit.iti.formal.util

/**
 * This interface signals, that a class/object supports additional user-defined metadata.
 *
 * @author Alexander Weigl
 * @version 1 (28.06.19)
 */
interface HasMetadata {
    fun <T> getMetadata(clazz: Class<T>): T?
    fun <T : Any> setMetadata(clazz: Class<T>, obj: T)
    fun getAllMetadata(): Collection<Any>
}

inline fun <reified T> HasMetadata.meta() = getMetadata(T::class.java)


/**
 * Default, hash map based implementation of metadata supports.
 *
 * Use by delegation:
 * ```
 *  class A : HasMetadata by HasMetadataImpl()
 * ```
 */
class HasMetadataImpl : HasMetadata {
    var metadata: HashMap<Class<*>, Any>? = null

    override fun <T> getMetadata(clazz: Class<T>): T? = metadata?.get(clazz) as? T

    override fun <T : Any> setMetadata(clazz: Class<T>, obj: T) {
        if (metadata == null) {
            metadata = HashMap()
        }
        metadata!![clazz] = obj
    }

    override fun getAllMetadata(): Collection<Any> {
        return metadata?.values ?: listOf()
    }
}

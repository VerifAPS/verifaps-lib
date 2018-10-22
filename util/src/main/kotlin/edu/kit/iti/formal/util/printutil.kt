package edu.kit.iti.formal.util

public fun <K, V, A : Appendable> Map<K, V>.joinInto(buffer: A,
                                                     separator: String = ",", prefix: String = "", postfix: String = "",
                                                     transform: (K, V) -> Unit) {
    val kv = entries.toList()
    buffer.append(prefix)
    if (isNotEmpty()) {
        for (i in 0 until size - 1) {
            transform(kv[i].key, kv[i].value)
            buffer.append(separator)
        }
        transform(kv[kv.lastIndex].key, kv[kv.lastIndex].value)
    }
    buffer.append(postfix)
}

public fun <T, A : Appendable> List<T>.joinInto(buffer: A,
                                                separator: String = ",", prefix: String = "", postfix: String = "",
                                                transform: (T) -> Unit) {
    buffer.append(prefix)
    if (isNotEmpty()) {
        for (i in 0 until size - 1) {
            transform(this[i])
            buffer.append(separator)
        }
        transform(this[lastIndex])
    }
    buffer.append(postfix)

}

/**
 *
 * @author Alexander Weigl
 * @version 1 (14.07.18)
 */
public operator fun CharSequence.times(i: Int): String {
    if(i<0) return ""
    val sb = StringBuilder()
    for (x in 1..i){
        sb.append(this)
    }
    return sb.toString()
}


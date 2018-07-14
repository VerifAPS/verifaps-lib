package edu.kit.iti.formal.automation

/**
 *
 * @author Alexander Weigl
 * @version 1 (14.07.18)
 */
public operator fun CharSequence.times(i: Int): Any {
    val sb = StringBuilder()
    for (x in 1..i){
        sb.append(this)
    }
    return sb.toString()
}

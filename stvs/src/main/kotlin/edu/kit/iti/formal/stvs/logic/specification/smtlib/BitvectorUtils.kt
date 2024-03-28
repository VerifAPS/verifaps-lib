package edu.kit.iti.formal.stvs.logic.specification.smtlib

import kotlin.math.pow

/**
 * Created by leonk on 12.02.2017.
 *
 * @author Leon Kaucher
 */
object BitvectorUtils {
    private val HEX_CHARS = charArrayOf('0', '1', '2', '3', '4', '5', '6', '7', '8', '9', 'A', 'B', 'C', 'D', 'E', 'F')

    /**
     * Convert an integer to its hex representation. The length specifies the number of output digits.
     * e.g. a length of 2 lets you convert positive numbers between 0 an 255 or numbers between -128
     * and 127 to their string representation Numbers are represented as a hexadecimal two's
     * complement.
     *
     * @param integer arbitrary integer
     * @param length Number of digits of output
     * @return hex representation with following format: #xABCD...
     */
    @JvmStatic
    fun hexFromInt(integer: Int, length: Int): String {
        var integer = integer
        if (integer < 0) {
            integer += 16.0.pow(length.toDouble()).toInt()
        }
        var result = ""
        for (i in 0 until length) {
            result = HEX_CHARS[integer % 16].toString() + result
            integer /= 16
        }
        return "#x$result"
    }

    /**
     * Converts a hex representation (hexadecimal two's complement) of an integer to an integer.
     *
     * @param hex hex representation with following format: #xABCD...
     * @param signed Defines if `hex` should be interpreted signed.
     * @return converted number
     */
    @JvmStatic
    fun intFromHex(hex: String?, signed: Boolean): Int {
        var hex = hex
        require(!(hex == null || !hex.matches("\\#x[a-fA-F0-9]+".toRegex()))) { "hex does not match expected format" }
        hex = hex.substring(2)
        var result = 0
        for (i in 0 until hex.length) {
            result *= 16
            result += (hex[i].toString() + "").toInt(16)
        }
        val full = 16.0.pow(hex.length.toDouble()).toInt()
        if (result >= full / 2 && signed) {
            result = -(full - result)
        }
        return result
    }
}

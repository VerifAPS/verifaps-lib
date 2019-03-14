package edu.kit.iti.formal.util

import java.util.*

/**
 *
 * @author Alexander Weigl
 * @version 1 (16.02.19)
 */
object Version {
    fun getVersionFiles(): List<Properties> {
        val urls = javaClass.classLoader.getResources("META-INF/version.property").toList()
        return urls.map { it.openStream().use { stream -> Properties().also { p -> p.load(stream) } } }
    }

    @JvmStatic
    fun main(args: Array<String>) {
        val keys = listOf(
                "Implementation-Title",
                "Implementation-Version",
                "Description",
                "Built-By",
                "Build-Timestamp",
                "Build-Revision",
                "Created-By",
                "Build-Jdk",
                "Build-OS")

        val jsonMode = ("--json" in args)
        val versions = getVersionFiles();

        if (jsonMode) {
            println(versions.map { it.json() }.joinToString(",\n", "[","]"))
        } else {
            versions.forEach { printHuman(it.toMap()) }
        }
    }

    private fun printHuman(toMap: Map<Any, Any>) {
        println("=" * 80)
        toMap.forEach { k, v ->
            println(String.format("%25s : %-35s", k, v))
        }
    }
}

private fun <K, V> Hashtable<K, V>.json(): String {
    return entries.joinToString(", ", "{","}") { (k,v)-> "\"$k\": \"$v\"" }
}

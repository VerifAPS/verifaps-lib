package edu.kit.iti.formal.stvs.logic.examples

import com.google.gson.GsonBuilder

/**
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 */
object ExamplesFacade {
    fun examples(): List<Example> {
        val res = javaClass.getResourceAsStream("/edu/kit/iti/formal/stvs/model/examples/examples.json")!!
            .reader()
        val json = GsonBuilder().setPrettyPrinting().create().fromJson(res, Array<Example>::class.java)
        return json.iterator().asSequence().toList()
    }
}

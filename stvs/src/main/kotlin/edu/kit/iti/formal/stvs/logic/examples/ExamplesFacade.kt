package edu.kit.iti.formal.stvs.logic.examples

import edu.kit.iti.formal.stvs.model.examples.Example
import java.util.*

/**
 * @author Alexander Weigl
 * @version 1 (01.04.17)
 */
object ExamplesFacade {
    @JvmStatic
    val examples: List<Example>
        get() {
            val loader = ServiceLoader.load(Example::class.java)
            return loader.iterator().asSequence().toList()
        }
}

package edu.kit.iti.formal.automation.ide

import java.util.function.Consumer

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.03.19)
 */
class EventBus {
    private val map
            = hashMapOf<Class<*>, MutableList<Consumer<*>>>()

    private fun <T> get(c: Class<T>): MutableList<Consumer<T>> {
        if (c !in map) {
            val n = ArrayList<Consumer<T>>() as MutableList<Consumer<T>>
            map.put(c, n.toMutableList())
        }
        return map[c] as MutableList<Consumer<T>>
    }

    public fun <T> register(c: Class<T>, f: Consumer<T>) {
        val seq = get(c)
        seq.add(f)
    }

    public fun register(obj: Any) {
        obj.javaClass.methods.forEach {
            if (it.getAnnotation(Subsribe::class.java) == null) {
                register(it)
            }
        }
    }

    public fun post(event: Any) {
        get(event.javaClass).forEach {
            it.accept(event)
        }
    }
}

val EVENT_BUS = EventBus()

@Retention(AnnotationRetention.RUNTIME)
annotation class Subsribe
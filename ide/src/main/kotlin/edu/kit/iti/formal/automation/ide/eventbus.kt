package edu.kit.iti.formal.automation.ide

import kotlin.reflect.KClass

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.03.19)
 */
class EventBus {
    private val map = hashMapOf<KClass<*>, MutableList<(Any) -> Unit>>()

    private fun <T> get(c: KClass<*>): MutableList<(T) -> Unit> {
        if (c !in map) {
            map[c] = arrayListOf()
        }
        return map[c] as MutableList<(T) -> Unit>
    }

    public fun <T : Any> register(c: KClass<T>, f: (T) -> Unit) {
        val seq: MutableList<(T) -> Unit> = get(c)
        seq.add(f)
    }

    public fun register(obj: Any) {
        obj.javaClass.methods.forEach {
            if (it.getAnnotation(Subsribe::class.java) == null) {
                register(it)
            }
        }
    }

    public inline fun <reified T : Any> listenTo(noinline f: (T) -> Unit) =
            register<T>(T::class, f)

    public fun <T : Any> post(event: T) {
        val seq: MutableList<(T) -> Unit> = get(event::class)
        seq.forEach { it(event) }
    }
}

val EVENT_BUS = EventBus()

@Retention(AnnotationRetention.RUNTIME)
annotation class Subsribe
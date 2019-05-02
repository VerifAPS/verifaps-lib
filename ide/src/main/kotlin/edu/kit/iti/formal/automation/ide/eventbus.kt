package edu.kit.iti.formal.automation.ide

import edu.kit.iti.formal.automation.st.ast.Position
import org.slf4j.LoggerFactory
import kotlin.reflect.KClass

/**
 *
 * @author Alexander Weigl
 * @version 1 (13.03.19)
 */
class EventBus {
    private val map = hashMapOf<KClass<*>, MutableList<(Any) -> Unit>>()

    private val logger = LoggerFactory.getLogger(EventBus::class.java)

    private fun <T> get(c: KClass<*>): MutableList<(T) -> Unit> {
        return map.computeIfAbsent(c) { arrayListOf() } as MutableList<(T) -> Unit>
    }

    fun <T : Any> register(c: KClass<T>, f: (T) -> Unit) {
        val seq: MutableList<(T) -> Unit> = get(c)
        seq.add(f)
    }

    fun register(obj: Any) {
        obj.javaClass.methods.forEach {
            if (it.getAnnotation(Subscribe::class.java) == null) {
                register(it)
            }
        }
    }

    public inline fun <reified T : Any> listenTo(noinline f: (T) -> Unit) =
            register<T>(T::class, f)

    public fun <T : Any> post(event: T) {
        logger.info("posting: $event")
        val seq: MutableList<(T) -> Unit> = get(event::class)
        seq.forEach { it(event) }
    }
}

val EVENT_BUS = EventBus()

data class EventGetetaUpdate(val text: String)

@Retention(AnnotationRetention.RUNTIME)
annotation class Subscribe
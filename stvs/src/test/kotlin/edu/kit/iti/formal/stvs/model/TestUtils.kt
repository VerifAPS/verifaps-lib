package edu.kit.iti.formal.stvs.model



/**
 * Created by Philipp on 20.01.2017.
 */
object TestUtils {
    fun <T> collectionsEqual(`as`: Collection<T>?, bs: Collection<T>?): Boolean {
        if (`as` === bs) {
            return true
        }
        if (`as` == null || bs == null) {
            return false
        }
        if (`as`.size != bs.size) {
            return false
        }

        return `as`.stream().allMatch { elem: T -> bs.stream().anyMatch { obj: T -> elem!!.equals(obj) } }
    }

    fun <T> assertCollectionsEqual(`as`: Collection<T>?, bs: Collection<T>?) {
        if (!collectionsEqual(`as`, bs)) {
            val error = String.format(
                "Unequal collections: %n" +
                        "Expected: %s%n" +
                        "Actual  : %s%n", `as`, bs
            )
            throw AssertionError(error)
        }
    }

    @Throws(Throwable::class)
    fun rethrowThreadUncheckedExceptions(runnable: Runnable) {
        val throwable = arrayOfNulls<Throwable>(1)
        val exceptionHandlerBefore = Thread.currentThread().uncaughtExceptionHandler
        Thread.currentThread().uncaughtExceptionHandler = Thread.UncaughtExceptionHandler { t, e -> throwable[0] = e }
        runnable.run()
        Thread.currentThread().uncaughtExceptionHandler = exceptionHandlerBefore
        if (throwable[0] != null) {
            throw throwable[0]!!
        }
    }
}

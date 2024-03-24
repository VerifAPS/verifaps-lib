package edu.kit.iti.formal.stvs

/**
 * @author Alexander Weigl
 * @version 1 (15.04.17)
 */
object StvsVersion {
    @JvmStatic
    val version: String
        get() = StvsVersion::class.java.getPackage().implementationVersion

    @JvmStatic
    val buildId: String
        get() = StvsVersion::class.java.getPackage().specificationVersion
    @JvmStatic
    val name: String
        get() = StvsVersion::class.java.getPackage().name

    @JvmStatic
    val windowTitle: String
        get() = "Structured Text Verification Studio - STVS"
}

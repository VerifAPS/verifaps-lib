package edu.kit.iti.formal.automation.testtables.builder

/**
 *
 * @author Alexander Weigl
 * @version 1 (07.03.18)
 */
abstract class AbstractTransformer() : TableTransformer {
    lateinit var model: ConstructionModel
    override fun accept(t: ConstructionModel) {
        this.model = t
        transform();
    }

    abstract fun transform()
}
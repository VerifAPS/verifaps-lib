package edu.kit.iti.formal.automation.plcopenxml

import org.jdom2.Element
import org.jdom2.filter.Filters
import org.jdom2.xpath.XPathExpression
import org.jdom2.xpath.XPathFactory

data class Trans(
        val from: Set<String> = setOf(),
        val to: Set<String> = setOf(),
        val condition: Set<String> = setOf(),
        val usedNodes: Set<String> = setOf())


class SfcElementAccess(val sfcElement: Element) {
    val CODESYS_ON_ENTRY = "a6b08bd8-b696-47e3-9cbf-7408b61c9ff8"
    val CODESYS_ON_EXIT = "a2621e18-7de3-4ea6-ae6d-89e9e0b7befd"
    val CODESYS_ON_STEP = "700a583f-b4d4-43e4-8c14-629c7cd3bec8"

    private val xpf = XPathFactory.instance()
    private val xpathFindRootStep = xpf.compile("./step[@initialStep='true']", Filters.element())
    private val xpathSteps = xpf.compile("./step", Filters.element())
    private val xpathTransitions = xpf.compile("./transition", Filters.element())
    private val xpathGetLocalId = createXPathWithId("./*[@localId=\$id]")
    private val xpathGetVendorData = createXPathWithId(".//attribute[@guid=\$id]")
    private val xpathFindActionsInActionBlock = createXPathWithId("./actionBlock[connectionPointIn/connection/@refLocalId=\$id]/action")


    val initialStep: Element by lazy { xpathFindRootStep.evaluateFirst(sfcElement) }
    val nodes by lazy { sfcElement.children.map { it.getAttributeValue("localId") to it }.toMap() }
    val access = HashMap<String, NodeAccess>()

    val steps: List<Step> by lazy { getElements("step") { Step(it) } }
    val transitions: List<Transition> by lazy { getElements("transition") { Transition(it) } }

    val pfork: List<ParallelFork> by lazy { getElements("simultaneousDivergence") { ParallelFork(it) } }
    val sfork: List<SelectiveFork> by lazy { getElements("selectionDivergence") { SelectiveFork(it) } }
    val pjoin: List<ParallelJoin> by lazy { getElements("simultaneousConvergence") { ParallelJoin(it) } }
    val sjoin: List<SelectiveJoin> by lazy { getElements("selectionConvergence") { SelectiveJoin(it) } }

    private fun <T> getElements(vararg names: String, func: (Element) -> T): List<T> = nodes.values.filter { it.name in names }.map(func)

    private fun createXPathWithId(expr: String): XPathExpression<Element> {
        val map = hashMapOf("id" to 0)
        return xpf.compile(expr, Filters.element(), map as Map<String, Any>)
    }

    fun getVendorSpecificAttribute(e: Element, guid: String): String? {
        xpathGetVendorData.setVariable("id", guid)
        val element = xpathGetVendorData.evaluateFirst(e)
        return element?.textTrim
    }


    open inner class NodeAccess(val entry: Element, expectedTag: String? = null) {
        val localId: String by lazy { entry.getAttributeValue("localId") }
        open val transitions: Collection<Trans>
            get() = arrayListOf()

        init {
            if (expectedTag != null && entry.name != expectedTag)
                throw IllegalArgumentException("Tag $expectedTag expected, but got ${entry.name}")
        }

        open fun transitionIncoming(): Collection<Trans> = arrayListOf()
        open fun transitionOutgoing(): Collection<Trans> = arrayListOf()
    }

    inner class JumpStep(e: Element) : NodeAccess(e, "jumpStep") {
        val jumpTo: String by lazy { entry.getAttributeValue("targetName") }

        override fun transitionIncoming(): Collection<Trans> {
            return listOf(Trans(from = setOf(jumpTo), usedNodes = setOf(localId)))
        }

        override fun transitionOutgoing(): Collection<Trans> {
            return listOf(Trans(to = setOf(jumpTo), usedNodes = setOf(localId)))
        }
    }

    inner class Step(e: Element) : NodeAccess(e, "step") {
        val name: String by lazy { entry.getAttributeValue("name") }
        val initial: Boolean by lazy {
            e.getAttributeValue("initialStep")?.toBoolean() ?: false
        }

        val onExit: String? by lazy { getVendorSpecificAttribute(e, CODESYS_ON_EXIT) }
        val onEntry: String? by lazy { getVendorSpecificAttribute(e, CODESYS_ON_ENTRY) }
        val onWhile: String?  by lazy { getVendorSpecificAttribute(e, CODESYS_ON_STEP) }
        val actionBlock: ActionBlock? by lazy { null }


        override fun transitionIncoming() =
                listOf(Trans(from = setOf(name), usedNodes = setOf(localId)))

        override fun transitionOutgoing() =
                listOf(Trans(to = setOf(name), usedNodes = setOf(localId)))
    }

    inner class ActionBlock(entry: Element) : NodeAccess(entry) {
        val actions by lazy {
            val actions = xpathFindActionsInActionBlock.evaluate(sfcElement)
            actions.map { action ->
                val qName = action.getAttributeValue("qualifier")
                val duration: String? = action.getAttributeValue("duration")
                val name = action.getChild("reference").getAttributeValue("name")
                if (duration != null)
                    "$name($qName)"
                else
                    "$name($qName,$duration)"
            }
        }
    }


    inner class ParallelFork(entry: Element) : NodeAccess(entry, "simultaneousDivergence") {
        override val transitions: Collection<Trans>
            get() = merge(transitionIncoming(), transitionOutgoing())

        override fun transitionIncoming(): Collection<Trans> {
            val inc = pointIn(entry)
            if (inc.size != 1) throw IllegalStateException()
            val it = inc[0].transitionIncoming()
            return it.map { it.copy(usedNodes = it.usedNodes + localId) }
        }

        override fun transitionOutgoing(): List<Trans> {
            //combine
            val a = pointOut(localId).flatMap { it.transitionOutgoing() }
            val usedNodes = a.flatMap { it.usedNodes } + localId
            val from = a.flatMap { it.from }
            val to = a.flatMap { it.to }
            val condition = a.flatMap { it.condition }
            return listOf(Trans(from.toSet(), to.toSet(), condition.toSet(), usedNodes.toSet()))
        }
    }


    inner class ParallelJoin(entry: Element) : SfcElementAccess.NodeAccess(entry, "simultaneousConvergence") {
        override val transitions: Collection<Trans>
            get() = merge(transitionIncoming(), transitionOutgoing())

        override fun transitionOutgoing(): Collection<Trans> {
            val inc = pointOut(localId)
            if (inc.size != 1) throw IllegalStateException()
            val it = inc[0].transitionOutgoing()
            return it.map { it.copy(usedNodes = it.usedNodes + localId) }
        }

        override fun transitionIncoming(): List<Trans> {
            //combine
            val a = pointIn(entry).flatMap { it.transitionIncoming() }
            val usedNodes = a.flatMap { it.usedNodes } + localId
            val from = a.flatMap { it.from }
            val to = a.flatMap { it.to }
            val condition = a.flatMap { it.condition }
            return listOf(Trans(from.toSet(), to.toSet(), condition.toSet(), usedNodes.toSet()))
        }
    }

    inner class SelectiveJoin(entry: Element) : NodeAccess(entry, "selectionConvergence") {
        override val transitions: Collection<Trans>
            get() = times(transitionIncoming(), transitionOutgoing())

        override fun transitionOutgoing() =
                pointOut(localId)
                        .flatMap { it.transitionOutgoing() }
                        .map { it.copy(usedNodes = it.usedNodes + localId) }

        override fun transitionIncoming(): List<Trans> =
                pointIn(entry)
                        .flatMap { it.transitionIncoming() }
                        .map { it.copy(usedNodes = it.usedNodes + localId) }
    }

    private fun times(from: Collection<Trans>, to: Collection<Trans>): Collection<Trans> {
        return from.flatMap { f ->
            to.map { t ->
                Trans(f.from + t.from, f.to + t.to, f.condition + t.condition,
                        t.usedNodes + f.usedNodes)
            }
        }
    }

    private fun merge(a: Collection<Trans>, b: Collection<Trans>): Collection<Trans> {
        val x = a.first()
        val y = b.first()
        return listOf(Trans(x.from + y.from,
                x.to + y.to, x.condition + y.condition,
                x.usedNodes + y.usedNodes))
    }

    inner class SelectiveFork(entry: Element) : NodeAccess(entry, "selectionDivergence") {
        override val transitions: Collection<Trans>
            get() = times(transitionIncoming(), transitionOutgoing())

        override fun transitionOutgoing() =
                pointOut(localId)
                        .flatMap { it.transitionOutgoing() }
                        .map { it.copy(usedNodes = it.usedNodes + localId) }

        override fun transitionIncoming(): List<Trans> =
                pointIn(entry)
                        .flatMap { it.transitionIncoming() }
                        .map { it.copy(usedNodes = it.usedNodes + localId) }
    }

    /**
     * Transition connects only two elements! No chaining allowed
     */
    inner class Transition(t: Element) : NodeAccess(t, "transition") {
        private val conditionRefId = xpf.compile("./condition/connectionPointIn/connection/@refLocalId", Filters.attribute())
        private val qExpression = ".//inVariable[@localId=\$id]/expression/text()"

        val conditionId by lazy {
            conditionRefId.evaluateFirst(t).value
                    ?: throw IllegalStateException("Following block does not have a transition guard:$t")
        }

        val condition: String by lazy {
            val q = xpf.compile(qExpression, Filters.text(), hashMapOf("id" to "id") as Map<String, Any>?)
            q.setVariable("id", conditionId)
            q.evaluateFirst(sfcElement).textTrim ?: "no condition found for $conditionId"
        }

        override val transitions: Collection<Trans>
            get() = times(transitionIncoming(), transitionOutgoing())

        override fun transitionIncoming(): Collection<Trans> =
                pointIn(entry).flatMap { it.transitionIncoming() }
                        .map {
                            it.copy(condition = it.condition + condition,
                                    usedNodes = it.usedNodes + localId + conditionId)
                        }

        override fun transitionOutgoing() =
                pointOut(localId).flatMap { it.transitionOutgoing() }
                        .map {
                            it.copy(condition = it.condition + condition,
                                    usedNodes = it.usedNodes + localId + conditionId)
                        }

    }

    public fun pointOut(localId: String): List<NodeAccess> {
        val xpathGetNext =
                createXPathWithId("./*[connectionPointIn/connection[@refLocalId=\$id]]")
        xpathGetNext.setVariable("id", localId)
        return xpathGetNext.evaluate(sfcElement).map { get<NodeAccess>(it) }
    }

    public fun pointIn(element: Element): List<NodeAccess> {
        val xpath = xpf.compile(
                "./connectionPointIn/connection/@refLocalId", Filters.attribute())
        return xpath.evaluate(element).map { nodes[it.value]!! }.map { get<NodeAccess>(it) }
    }


    private fun <T : NodeAccess> get(e: Element): T = access.computeIfAbsent(e.getAttributeValue("localId")) { factory(e) as T } as T

    private fun <T : NodeAccess> get(e: String): T = access.computeIfAbsent(e) { factory(nodes[it]!!) as T } as T

    private fun <T : NodeAccess> factory(e: Element): T {
        return when (e.name) {
            "step" -> Step(e)
            "transition" -> Transition(e)
            "selectionDivergence" -> SelectiveFork(e)
            "selectionConvergence" -> SelectiveJoin(e)
            "simultaneousDivergence" -> ParallelFork(e)
            "simultaneousConvergence" -> ParallelJoin(e)
            "jumpStep" -> JumpStep(e)
            else -> throw IllegalStateException(e.name)
        } as T
    }
}
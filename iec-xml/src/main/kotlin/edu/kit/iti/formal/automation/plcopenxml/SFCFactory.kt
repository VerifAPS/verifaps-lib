package edu.kit.iti.formal.automation.plcopenxml

/*-
 * #%L
 * iec-xml
 * %%
 * Copyright (C) 2017 Alexander Weigl
 * %%
 * This program isType free software: you can redistribute it and/or modify
 * it under the terms of the GNU General Public License as
 * published by the Free Software Foundation, either version 3 of the
 * License, or (at your option) any later version.
 *
 * This program isType distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a clone of the GNU General Public
 * License along with this program.  If not, see
 * <http://www.gnu.org/licenses/gpl-3.0.html>.
 * #L%
 */

import edu.kit.iti.formal.automation.IEC61131Facade
import edu.kit.iti.formal.automation.parser.ErrorReporter
import edu.kit.iti.formal.automation.st.ast.*
import edu.kit.iti.formal.automation.st.ast.BooleanLit.Companion.LTRUE
import org.jdom2.Attribute
import org.jdom2.Element
import org.jdom2.Text
import org.jdom2.filter.Filters
import org.jdom2.xpath.XPathExpression
import org.jdom2.xpath.XPathFactory
import java.util.*
import java.util.function.Function
import java.util.function.Supplier

/**
 * @author Alexander Weigl
 * @version 1 (30.05.17)
 */
class SFCFactory(private val sfcElement: Element) : Supplier<SFCImplementation> {
    private val nodes = HashMap<String, Node>()

    //private Set<SFCStep> sfcSteps = new HashSet<>();
    //private Set<SFCTransition> sfcTransition = new HashSet<>();
    private val sfc = SFCImplementation()
    private val network = SFCNetwork()
    private val usedTransitions = LinkedList<Node>()

    private fun traverse() {
        val rootStep = xpathFindRootStep.evaluateFirst(sfcElement)
        val matchAll = xpf.compile("./*", Filters.element())
        for (e in matchAll.evaluate(sfcElement)) {
            if (e.name == "actionBlock" || e.name == "inVariable")
                continue // Action blocks are handled later by the step conversion.
            val n = factory<Node>(e)
            nodes[n.localId!!] = n
        }

        val getConnectPoints = xpf.compile("./connectionPointIn/connection/@refLocalId", Filters.attribute())
        //resolve links
        for (e in matchAll.evaluate(sfcElement)) {
            if (e.name == "actionBlock" || e.name == "inVariable")
                continue // Action blocks are handled later by the step conversion.
            val idIncoming = e.getAttributeValue("localId")
            for (a in getConnectPoints.evaluate(e)) {
                val idOutgoing = a.value
                val incoming = nodes[idIncoming]
                val outgoing = nodes[idOutgoing]

                if (incoming != null && outgoing != null) {
                    incoming.incoming.add(outgoing)
                    outgoing.outgoing.add(incoming)
                }
            }
        }
    }

    private fun <T> factory(e: Element): T {
        /*
        step, macroStep, transition, selectionDivergence
        selectionConvergence, simultaneousDivergence, simultaneousConvergence
         */
        when (e.name) {
            "step" -> return Step(e) as T
            "transition" -> return Transition(e) as T
            "selectionDivergence" -> return Divergence(e) as T
            "selectionConvergence" -> return Convergence(e) as T
            "simultaneousDivergence" -> return Divergence(e, true) as T
            "simultaneousConvergence" -> return Convergence(e, true) as T
            "jumpStep" -> return JumpStep(e) as T
            else -> throw IllegalStateException(e.name)
        }
    }

    override fun get(): SFCImplementation {
        traverse()
        translate()

        // only simult. div/conv used, use the rest!
        var n = ArrayList(nodes.values)
        n.removeAll(usedTransitions)
        for (node in n) {
            if (node is Transition) {
                node.insertIntoNetwork()
            }
        }

        n = ArrayList(nodes.values)
        n.removeAll(usedTransitions)
        //System.out.printf("%s%n", n);

        sfc.networks.add(network)
        return sfc
    }

    private fun translate() {
        nodes.values
                .filter { n -> n is Step }
                .map { Step::class.java.cast(it) }
                .map { it.createSFCStep() }
                .forEach { network.steps.add(it) }

        nodes.values.stream()
                .filter { it is Divergence }
                .map { Divergence::class.java.cast(it) }
                .forEach { it.insertIntoNetwork() }

        nodes.values.stream()
                .filter { it is Convergence }
                .map { Convergence::class.java.cast(it) }
                .forEach { it.insertIntoNetwork() }
    }

    private fun parseActionBlock(localId: String?,
                                 events: MutableList<SFCStep.AssociatedAction>) {
        xpathFindActionsInActionBlock.setVariable("id", localId)
        val actions = xpathFindActionsInActionBlock.evaluate(sfcElement)
        for (action in actions) {
            val qName = action.getAttributeValue("qualifier")
            val q = SFCActionQualifier.fromName(qName)
            if (q != null)
                if (q.qualifier.hasTime) {
                    q.time = (IEC61131Facade.expr(action.getAttributeValue("duration")))
                    //TODO support for indicator?
                }

            val `var` = action.getChild("reference").getAttributeValue("name")
            events.add(SFCStep.AssociatedAction(q, `var`))
        }
    }

    fun nameToStep(steps: Collection<String>): Set<SFCStep> {
        return steps
                .map { network.getStep(it) }
                .filter { o -> o.isPresent }
                .map { o -> o.get() }
                .toHashSet()
    }

    private fun createSFCTransition(fromName: List<String>, toName: List<String>,
                                    guardsFrom: List<String>, guardsTo: List<String>): SFCTransition {
        val t = SFCTransition()
        val st = nameToStep(toName)
        t.to = (st)
        val sf = nameToStep(fromName)
        t.from = (sf)
        sf.forEach { s -> s.outgoing.add(t) }
        st.forEach { s -> s.incoming.add(t) }

        val guards = HashSet(guardsFrom)
        guards.addAll(guardsTo)
        if (guards.size > 0) {
            val guard = guards.joinToString(" AND ")
            try {
                t.guard = (IEC61131Facade.expr(guard))
            } catch (e: ErrorReporter.IEC61131ParserException) {
                System.err.println(guard)
                System.err.println(e.message)
            }

        } else {
            t.guard = LTRUE
        }
        return t
    }

    inner class Transition(t: Element) : Node(t) {
        var conditions: String = "<empty>"

        init {
            val a = qRefLocalId.evaluateFirst(t)
            if (a != null) {
                qExpression.setVariable("id", a.value)
                val textTrim = qExpression.evaluateFirst(sfcElement)
                conditions = textTrim.text
            } else {
                System.err.println("Following element does not have a transition guard:$t")
            }
        }

        fun insertIntoNetwork() {
            if (usedTransitions.contains(this)) {
                return
            }
            assert(outgoing.size == 1)
            assert(incoming.size == 1)

            val fromName = getTransitions(true)
            val toName = getTransitions(false)

            assert(outgoing.size == toName.size)
            //assert incoming.size() == fromName.size();

            for (from in fromName) {
                usedTransitions.addAll(from.usedNodes)
                for (to in toName) {
                    createSFCTransition(from.steps, to.steps, from.guards, to.guards)
                    usedTransitions.addAll(to.usedNodes)
                }
            }
        }


        override fun getTransitions(incdirection: Boolean): List<PseudoTransition> {
            val ref = if (incdirection) incoming else outgoing
            if (ref.size == 0)
                System.err.println("Transition " + this + " does not have an incoming or outgoing connection")

            return ref
                    .flatMap { it.getTransitions(incdirection) }
                    .map { pt ->
                        pt.addGuard(conditions)
                        pt.usedNodes.add(this)
                        pt
                    }
        }
    }

    //TODO @EqualsAndHashCode(of = arrayOf("localId"))
    //TODO @ToString(exclude = arrayOf("outgoing", "incoming"))
    open inner class Node(e: Element) : Comparable<Step> {
        var entry: Element? = null
        var name: String?
        var outgoing: MutableSet<Node> = HashSet()
        var incoming: MutableSet<Node> = HashSet()
        var localId: String? = null

        val next: List<Element>
            get() {
                xpathGetNext.setVariable("id", localId)
                return xpathGetNext.evaluate(sfcElement)
            }

        init {
            localId = e.getAttributeValue("localId")
            name = e.getAttributeValue("name")
            assert(localId != null) { "@localId was not given in " + e.toString() }
        }

        override fun compareTo(o: Step): Int {
            if (name == null || o.name == null)
                return 0
            return name!!.compareTo(o.name!!)
        }

        open fun getTransitions(incoming: Boolean): List<PseudoTransition> {
            return emptyList()
        }

        fun getSteps(direction: Function<Node, Set<Node>>): Set<String> {
            val stepsFrom = HashSet<String>()
            val queue = LinkedList<Node>()
            queue.addAll(direction.apply(this))
            while (!queue.isEmpty()) {
                val n = queue.remove()
                if (n is Step) {
                    stepsFrom.add(n.name!!)
                } else {
                    if (n is JumpStep) {
                        stepsFrom.add(n.jumpTo)
                    } else {
                        queue.addAll(direction.apply(n))
                    }
                }
            }
            return stepsFrom
        }

        override fun equals(o: Any?): Boolean {
            if (this === o) return true
            if (o == null || javaClass != o.javaClass) return false
            if (!super.equals(o)) return false

            val node = o as Node?

            return localId == node!!.localId
        }

        override fun hashCode(): Int {
            var result = super.hashCode()
            result = 31 * result + localId!!.hashCode()
            return result
        }

        //TODO @Value
        inner class PseudoTransition(val steps: ArrayList<String> = ArrayList<String>(5),
                                     val guards: ArrayList<String> = ArrayList<String>(5),
                                     val usedNodes: HashSet<Node> = HashSet<Node>(5)) {

            constructor(name: String, conditions: String, used: Node) : this(name, used) {
                guards.add(conditions)
            }

            constructor(pt: PseudoTransition) : this() {
                steps.addAll(pt.steps)
                guards.addAll(pt.guards)
                usedNodes.addAll(pt.usedNodes)
            }

            constructor(name: String, usedNode: Node) : this(usedNode) {
                steps.add(name)
            }

            constructor(used: Node) : this() {
                usedNodes.add(used)
            }

            fun addGuard(conditions: String) {
                guards.add(conditions)
            }
        }
    }

    //TODO @ToString(callSuper = true)
    inner class JumpStep(e: Element) : Node(e) {
        var jumpTo: String

        init {
            jumpTo = e.getAttributeValue("targetName")
        }

        override fun getTransitions(incoming: Boolean): List<PseudoTransition> {
            return listOf(PseudoTransition(jumpTo, this))
        }
    }

    //TODO @ToString(callSuper = true)
    inner class Step(e: Element) : Node(e) {
        var initial: Boolean = false
        var onExit: String? = null
        var onEntry: String? = null
        var onWhile: String? = null

        init {
            onWhile = getVendorSpecificAttribute(e, CODESYS_ON_STEP)
            onEntry = getVendorSpecificAttribute(e, CODESYS_ON_ENTRY)
            onExit = getVendorSpecificAttribute(e, CODESYS_ON_EXIT)

            val initialStep = e.getAttributeValue("initialStep")
            initial = initialStep != null && java.lang.Boolean.valueOf(initialStep)
            //TODO onExit = getVendorSpecificAttribute(e, CODESYS_ON_STEP);
            //TODO onEntry = getVendorSpecificAttribute(e, CODESYS_ON_STEP);
        }

        override fun getTransitions(incoming: Boolean): List<PseudoTransition> {
            return listOf(PseudoTransition(name!!, this))
        }

        fun createSFCStep(): SFCStep {
            val ss = SFCStep()
            ss.isInitial = initial
            ss.name = name!!
            parseActionBlock(localId, ss.events)

            if (onWhile != null && !onWhile!!.isEmpty())
                ss.events.add(SFCStep.AssociatedAction(SFCActionQualifier.NON_STORED, onWhile!!))

            if (onExit != null && !onExit!!.isEmpty())
                ss.events.add(SFCStep.AssociatedAction(SFCActionQualifier.FALLING, onExit!!))

            if (onEntry != null && !onEntry!!.isEmpty())
                ss.events.add(SFCStep.AssociatedAction(SFCActionQualifier.RAISING, onEntry!!))

            return ss
        }
    }

    //TODO @ToString(callSuper = true)
    inner class Convergence : Node {
        var parallel: Boolean = false

        constructor(e: Element) : super(e) {}

        constructor(e: Element, b: Boolean) : super(e) {
            parallel = true
        }

        override fun getTransitions(inc: Boolean): List<PseudoTransition> {
            val ref = if (inc) incoming else outgoing
            if (parallel) {
                if (inc) {
                    val pt = PseudoTransition(this)
                    for (n in ref) {
                        for (p in n.getTransitions(inc)) {
                            pt.steps.addAll(p.steps)
                            pt.guards.addAll(p.guards)
                            pt.usedNodes.addAll(p.usedNodes)
                        }
                    }
                    return listOf(pt)
                }
            }
            return ref
                    .flatMap { it.getTransitions(inc) }
                    .map {
                        it.usedNodes.add(this)
                        it
                    }
        }

        fun insertIntoNetwork() {
            if (usedTransitions.contains(this)) {
                return
            }
            // joining the edge
            //assert incoming.stream().allMatch(s -> s instanceof Transition);
            //assert outgoing.stream().allMatch(s -> s instanceof Transition);
            assert(outgoing.size == 1)

            val fromName = getTransitions(true)
            val toName = getTransitions(false)

            assert(parallel || fromName.size >= incoming.size)
            assert(toName.size >= outgoing.size)

            for (from in fromName) {
                usedTransitions.addAll(from.usedNodes)
                for (to in toName) {
                    createSFCTransition(from.steps, to.steps, from.guards, to.guards)
                    usedTransitions.addAll(to.usedNodes)
                }
            }
        }
    }

    //TODO @ToString(callSuper = true)
    inner class Divergence @JvmOverloads constructor(e: Element, var parallel: Boolean = false) : Node(e) {

        override fun getTransitions(incdirection: Boolean): List<PseudoTransition> {
            val ref = if (incdirection) incoming else outgoing
            if (parallel && !incdirection) {
                val pt = PseudoTransition(this)
                for (n in ref) {
                    for (p in n.getTransitions(incdirection)) {
                        pt.steps.addAll(p.steps)
                        pt.guards.addAll(p.guards)
                    }
                }
                return listOf(pt)
            }
            return ref
                    .flatMap { it.getTransitions(incdirection) }
                    .map {
                        it.usedNodes.add(this)
                        it
                    }
        }


        fun insertIntoNetwork() {
            if (usedTransitions.contains(this)) {
                return
            }

            // splitting the edge!
            //assert outgoing.stream().allMatch(s -> s instanceof Transition);
            //assert incoming.stream().allMatch(s -> s instanceof Transition);
            assert(outgoing.size >= 1)
            assert(incoming.size == 1)

            val fromName = getTransitions(true)
            val toName = getTransitions(false)

            assert(parallel || outgoing.size <= toName.size)
            assert(incoming.size <= fromName.size)

            for (from in fromName) {
                usedTransitions.addAll(from.usedNodes)
                for (to in toName) {
                    createSFCTransition(from.steps, to.steps, from.guards, to.guards)
                    usedTransitions.addAll(to.usedNodes)
                }
            }


        }
    }

    companion object {
        val CODESYS_ON_ENTRY = "a6b08bd8-b696-47e3-9cbf-7408b61c9ff8"
        val CODESYS_ON_EXIT = "a2621e18-7de3-4ea6-ae6d-89e9e0b7befd"
        private val CODESYS_ON_STEP = "700a583f-b4d4-43e4-8c14-629c7cd3bec8"
        private val xpf = XPathFactory.instance()
        private val xpathFindRootStep: XPathExpression<Element>
        private val xpathGetLocalId: XPathExpression<Element>
        private val xpathGetVendorData: XPathExpression<Element>
        private val xpathGetNext: XPathExpression<Element>
        private val qRefLocalId: XPathExpression<Attribute>
        private val qExpression: XPathExpression<Text>
        private val xpathFindActionsInActionBlock: XPathExpression<Element>

        init {
            /*
            All queries are relative to <SFC> root element.
         */
            xpathFindRootStep = xpf.compile("./step[@initialStep='true']", Filters.element())


            val id = HashMap<String, Any>()// Collections.singletonMap("id", null);
            id["id"] = 0

            xpathGetLocalId = xpf.compile("./*[@localId=\$id]",
                    Filters.element(), id)

            xpathGetNext = xpf.compile("./*[connectionPointIn/connection[@refLocalId=\$id]]",
                    Filters.element(), id)

            xpathGetVendorData = xpf.compile(".//attribute[@guid=\$id]",
                    Filters.element(), id)

            qRefLocalId = xpf.compile("./condition/connectionPointIn/connection/@refLocalId",
                    Filters.attribute())
            qExpression = xpf.compile(".//inVariable[@localId=\$id]/expression/text()",
                    Filters.text(), id)

            xpathFindActionsInActionBlock = xpf.compile("./actionBlock[connectionPointIn/connection/@refLocalId=\$id]/action",
                    Filters.element(), id)
        }

        private fun getVendorSpecificAttribute(e: Element, guid: String): String {
            xpathGetVendorData.setVariable("id", guid)
            val element = xpathGetVendorData.evaluateFirst(e)
            return if (element == null) "" else element.textTrim
        }
    }
}
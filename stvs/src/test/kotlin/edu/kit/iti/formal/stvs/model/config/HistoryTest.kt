package edu.kit.iti.formal.stvs.model.config

import org.junit.jupiter.api.Assertions
import org.junit.jupiter.api.BeforeEach
import org.junit.jupiter.api.Test
import kotlin.test.assertFailsWith

/**
 * @author Benjamin Alt
 */
class HistoryTest {
    private var history: History? = null

    @BeforeEach
    fun setUp() {
        history = History()
    }

    @Test
    fun testBufferSize() {
        Assertions.assertEquals(0, history!!.filenames.size.toLong())
        for (i in 0 until History.HISTORY_DEPTH * 2) {
            history!!.addFilename("filePath$i")
        }
        Assertions.assertEquals(History.HISTORY_DEPTH.toLong(), history!!.filenames.size.toLong())
    }

    @Test
    fun testConstructor() {
        val filePaths = ArrayList<String>()
        filePaths.add("CodeOne")
        filePaths.add("CodeTwo")
        filePaths.add("SpecOne")
        history = History(filePaths)
        val filePathsAfter: List<String> = history!!.filenames
        Assertions.assertEquals(filePathsAfter[0], "CodeOne")
        Assertions.assertEquals(filePathsAfter[1], "CodeTwo")
        Assertions.assertEquals(filePathsAfter[2], "SpecOne")
    }

    @Test//(expected = IllegalArgumentException::class)
    fun testConstructorException() {
        val codePaths = ArrayList<String>()
        for (i in 0 until History.HISTORY_DEPTH * 2) {
            codePaths.add("SomeCode$i")
        }
        assertFailsWith<IllegalArgumentException> {
            history = History(codePaths)
        }
    }

    @Test
    fun testAddSpecFilename() {
        history!!.addFilename("someSpec")
        Assertions.assertEquals(history!!.filenames[0], "someSpec")
    }

    @Test
    fun testSetAll() {
        testConstructor()
        val clone = History()
        clone.setAll(history!!)
        Assertions.assertEquals(history, clone)
    }

    @Test
    fun testEquals() {
        testConstructor()
        val filePaths = ArrayList<String>()
        filePaths.add("CodeOne")
        filePaths.add("CodeTwo")
        filePaths.add("SpecOne")
        val identical = History(filePaths)
        Assertions.assertEquals(history, identical)
        Assertions.assertNotEquals(null, history)
        Assertions.assertEquals(history, history)
        identical.filenames.add("Another filename!")
        Assertions.assertNotEquals(history, identical)
    }

    @Test
    fun testHashCode() {
        testConstructor()
        val filePaths = ArrayList<String>()
        filePaths.add("CodeOne")
        filePaths.add("CodeTwo")
        filePaths.add("SpecOne")
        val identical = History(filePaths)
        Assertions.assertEquals(history.hashCode().toLong(), identical.hashCode().toLong())
        Assertions.assertEquals(history.hashCode().toLong(), history.hashCode().toLong())
        identical.filenames.add("Another filename!")
        Assertions.assertNotEquals(history.hashCode().toLong(), identical.hashCode().toLong())
    }
}

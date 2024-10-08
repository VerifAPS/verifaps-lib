package edu.kit.iti.formal.stvs.model.code

/**
 * A block of source code. Although code folding is not supported by the view, this class may be
 * used in future versions to implement code folding.
 *
 * @author Philipp
 */
class FoldableCodeBlock
/**
 * Create a new FoldableCodeBlock from a start and an end line index (inclusive).
 * @param start The index of the first line of the block
 * @param end The index of the last line of the block
 */ internal constructor(
    /**
     * Get the index of the last line of the code block.
     * @return The index of the first line of the code block
     */
    @JvmField val startLine: Int,
    /**
     * Get the index of the first line of the code block.
     * @return The index of the first line of the code block
     */
    @JvmField val endLine: Int
) {
    override fun equals(obj: Any?): Boolean {
        if (this === obj) {
            return true
        }
        if (obj !is FoldableCodeBlock) {
            return false
        }

        val that = obj

        return startLine == that.startLine && endLine == that.endLine
    }

    override fun hashCode(): Int {
        var result = startLine
        result = 31 * result + endLine
        return result
    }
}

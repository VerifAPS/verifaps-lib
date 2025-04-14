package edu.kit.iti.formal.stvs.model.code

/**
 * A block of source code. Although code folding is not supported by the view, this class may be
 * used in future versions to implement code folding.
 *
 * @author Philipp
 */
data class FoldableCodeBlock(
    /**
     * Get the index of the last line of the code block.
     * @return The index of the first line of the code block
     */
    val startLine: Int,
    /**
     * Get the index of the first line of the code block.
     * @return The index of the first line of the code block
     */
    val endLine: Int
)

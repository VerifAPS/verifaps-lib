package edu.kit.iti.formal.util

interface Array2d<T> {
    fun columns(): Int
    fun rows(): Int
    operator fun get(col: Int, row: Int): T
    operator fun set(col: Int, row: Int, value: T)
}

/*
class Array2D<T>(val columns: Int, val rows: Int, init: T) : Array2d<T> {
    private val data = Array(columns * rows) { init }

    override fun columns(): Int = columns
    override fun rows(): Int = rows

    override fun get(col: Int, row: Int): T {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

    override fun set(col: Int, row: Int, value: T) {
        TODO("not implemented") //To change body of created functions use File | Settings | File Templates.
    }

}


internal fun pos2d(rows: Int, columns: Int, row: Int, col: Int): Int = col + row * columns

internal fun pos2d(columns: Int, rows: Int, pos: Int): Pair<Int, Int> = (pos / rows) to (pos % rows)

/**
 * Created on 22.10.2018
 * @author weigl
 */
data class Grid<T>(private var data: ArrayList<T> = arrayListOf()) : Array2d<T> {
    var columns: Int = 0;
    var rows: Int = 0
    constructor(columns: Int, rows: Int, ) {
        ensureSize(rows,columns)
    }

    override fun columns(): Int = columns
    override fun rows(): Int = rows
    override fun set(col: Int, row: Int, value: T) {
        ensureField(col, row)
        data[pos2d(rows, columns, row, col)] = value
    }

    fun ensureField(col: Int, row: Int)

    fun ensureSize(rows: Int, columns: Int: Int, empty: T) {
        data.ensureCapacity(height * width)
        for (i in 0..(height * width) - data.size)
            data.add(empty)
    }

    fun get(col: Int, row: Int): T? {

    }

    fun columnwise(col: Int): Sequence<T> {
        return
    }

    fun rowwise(row: Int): Sequence<T> {
        return
    }
}
*/
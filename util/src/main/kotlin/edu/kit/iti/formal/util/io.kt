package edu.kit.iti.formal.util

import java.nio.file.Files
import java.nio.file.Path

/**
 *
 * @author Alexander Weigl
 * @version 1 (04.05.19)
 */

fun Path.inputStream() = Files.newInputStream(this)

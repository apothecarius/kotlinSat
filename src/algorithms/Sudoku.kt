package algorithms

import materials.ClauseSetWatchedLiterals
import materials.ClauseWatchedLiterals
import materials.Literal
import materials.Variable

typealias FieldPossibilities = Array<Variable>
/**
 * Allows to find sudoku SAT variables by x coordinate, y coordinate and assignment
 * Note that some textual methods use 1..9 indices, but this object itself uses 0..8
 * Can be instantiated with Sudoku.makeVariables()
 */
typealias SudokuVariableSet = Array<Array<FieldPossibilities>>

/**
 * Returns coordinates of sudoku field (within [0..8]**2)
 * Blocktype can be in [1..3] for column,row or square
 */
private fun SudokuVariableSet.getSudokuFieldCoord(blockIdx: Int, fieldIdx: Int, blockType: Int):Pair<Int,Int> {
    assert(blockIdx in 0..8)
    assert(fieldIdx in 0..8)
    assert(blockType in 1..3)

    return when (blockType) {
        1 -> Pair(blockIdx, fieldIdx)
        2 -> Pair(fieldIdx, blockIdx)
        3 -> {
            val bx = blockIdx % 3
            val by = (blockIdx-bx) / 3
            val dx = fieldIdx % 3
            val dy = (fieldIdx - dx) / 3
            Pair(bx*3+dx, by*3+dy)
        }
        else -> throw Error("Only three block types in a Sudoku")
    }
}
private fun SudokuVariableSet.getSudokuField(blockIdx: Int, fieldIdx: Int, blockType: Int): FieldPossibilities {
    with(this.getSudokuFieldCoord(blockIdx,fieldIdx,blockType)){
        return this@getSudokuField[first][second]
    }

}


/**
 * This class serves to model sudoku problems as CNF formulae and solve them
 * with the sat solver
 * The constructor can be given a set of fixed field assignments with both
 * x and y indices in [1,9]]
 *
 * TODO: Add functions for intuitive input (sudoku puzzle statement) and output (print result as integer array or string)
 */
class Sudoku(fixedVars: Array<Array<Int>>) : ClauseSetWatchedLiterals(makeSudokuFormula(fixedVars)) {
    //TODO string based constructor or from a file
    fun printTrueAssignments() {
        for (vari in this.getPresentVariables()) {
            if (!vari.isUnset && vari.boolSetting!!) {
                println(vari.id)
            }
        }
    }

    companion object {
        private fun makeVarId(x: Int, y: Int, assignment: Int): String =
                (x.toString() + "x" + y.toString() + ":" + assignment.toString())

        fun makeSudokuFormula(fixedVars: Array<Array<Int>>): Array<ClauseWatchedLiterals> {
            val vars: SudokuVariableSet = makeVariables()
            //base sudoku rules can be explained with two rules
            //R1a + R1b: Every field must have exactly one assignment
            // (split into R1a"at least one assignment" and R1b"at most one assignment"
            //R2: Every block/column/row must contain every assignment once
            // also split into "have every one" and "they must be unique per block"
            return (ensureFieldsHaveSomeAssignment(vars) +
                    ensureFieldsHaveAtMostOneAssignment(vars) +
                    ensureBlocksHaveEveryAssignment(vars) +
                    ensureBlocksHaveUniqueAssignments(vars) +
                    fixAssignments(fixedVars, vars)
                    ).toList().toTypedArray()
        }

        /**
         * Returns rules that enforce assigning a specific field to a specific number
         */
        private fun fixAssignments(fixedVars: Array<Array<Int>>, knownVars: SudokuVariableSet): Sequence<ClauseWatchedLiterals> {
            return sequence {
                for (fix in fixedVars) {
                    assert(fix.size == 3)
                    { "Assignments must have 3 numbers between 1 and 9" }
                    fix.forEach {
                        assert(it in 1..9)
                        { "Assignments must be between 1 and 9" }
                    }
                    //values are given as [1..9]
                    val theVar = knownVars[fix[0] - 1][fix[1] - 1][fix[2] - 1]
                    ClauseWatchedLiterals(Literal(theVar, true))
                }
            }
        }


        private fun makeVariables(): SudokuVariableSet {
            //a 9x9 field matrix with 9 possibilities each
            val matrix = sequence<Array<Array<Variable>>> {
                for (x: Int in 1..9) //x coordinate
                {
                    //one column of 9 fields
                    val column: Array<Array<Variable>> = sequence {
                        for (y: Int in 1..9) // y coordinate
                        {
                            //one field with 9 possible assignments
                            val field: Array<Variable> = sequence {
                                for (b: Int in 1..9) // what is assigned in this slot
                                {
                                    yield(Variable(makeVarId(x, y, b)))
                                }
                            }.toList().toTypedArray()
                            assert(field.size == 9)
                            yield(field)
                        }
                    }.toList().toTypedArray()
                    assert(column.size == 9)
                    yield(column)
                }
            }.toList().toTypedArray()
            assert(matrix.size == 9)
            return matrix
        }

        private fun ensureFieldsHaveSomeAssignment(vars: SudokuVariableSet): Sequence<ClauseWatchedLiterals> {
            return do9ToPowerNTimes { x, y ->
                val thisFieldsAssignments: Array<Literal> = vars[x][y].map { Literal(it, true) }.toTypedArray()
                sequenceOf(ClauseWatchedLiterals(thisFieldsAssignments))
            }
        }


        private fun ensureFieldsHaveAtMostOneAssignment(vars: SudokuVariableSet): Sequence<ClauseWatchedLiterals> {
            return do9ToPowerNTimes { x, y, i, j ->
                if (i == j) {
                    emptySequence<ClauseWatchedLiterals>()
                }
                val curRule = ClauseWatchedLiterals(arrayOf(
                        Literal(vars[x][y][i], false),
                        Literal(vars[x][y][j], false)
                ))
                sequenceOf(curRule)
            }
        }

        /**
         * Calls the given function in 2 loops with number 0..8 each and returns the results in one sequence
         */
        private fun <T> do9ToPowerNTimes(f: ((Int, Int) -> Sequence<T>)): Sequence<T> {
            return sequence {
                for (x in 0..8) {
                    for (y in 0..8) {
                        yieldAll(f(x, y))
                    }
                }
            }
        }

        /**
         * Calls the given function in 4 loops with number 0..8 each and returns the results in one sequence
         */
        private fun <T> do9ToPowerNTimes(f: ((Int, Int, Int, Int) -> Sequence<T>)): Sequence<T> {
            return sequence {
                for (a in 0..8) {
                    for (b in 0..8) {
                        for (c in 0..8) {
                            for (d in 0..8) {
                                yieldAll(f(a, b, c, d))
                            }
                        }
                    }
                }
            }
        }

        private fun ensureBlocksHaveEveryAssignment(vars: SudokuVariableSet): Sequence<ClauseWatchedLiterals> {
            //val retu: MutableList<materials.ClauseWatchedLiterals> = mutableListOf()

            return do9ToPowerNTimes { assignment:Int,blockIdx:Int ->

                sequence{
                    //in row x, any field must have 'assignment'
                    ClauseWatchedLiterals((0..8).map { fieldIdx ->
                        Literal(vars[blockIdx][fieldIdx][assignment], true)
                    }.toTypedArray())
                    //same for columns
                    ClauseWatchedLiterals((0..8).map { fieldIdx ->
                        Literal(vars[fieldIdx][blockIdx][assignment], true)
                    }.toTypedArray())

                    //same for squares
                    ClauseWatchedLiterals((0..8).map { fieldIdx ->
                        val squaresField = vars.getSudokuField(blockIdx, fieldIdx, 3)
                        Literal(squaresField[assignment], true)
                    }.toTypedArray())
                }
            }
        }

        private fun ensureBlocksHaveUniqueAssignments(vars: SudokuVariableSet): Sequence<ClauseWatchedLiterals> {
            return do9ToPowerNTimes { blockIdx, blocksField, blocksOtherField, assignment ->
                if (blocksOtherField == blocksField) {
                    emptySequence<ClauseWatchedLiterals>()
                }
                sequence{
                    for (blockType in 1..3) {
                        val field = vars.getSudokuField(blockIdx, blocksField, blockType)
                        val otherField = vars.getSudokuField(blockIdx, blocksOtherField, blockType)

                        ClauseWatchedLiterals(arrayOf(
                                Literal(field[assignment], false),
                                Literal(otherField[assignment], false)
                        ))
                    }
                }
            }
        }
    }
}


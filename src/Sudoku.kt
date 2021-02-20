import org.junit.Test
import kotlin.test.assertEquals

/**
 * Allows to find sudoku SAT variables by x coordinate, y coordinate and assignment
 * Note that some textual methods use 1..9 indices, but this object itself uses 0..8
 */
typealias SudokuVariableSet = Array<Array<Array<Variable>>>
/**
 * This class serves to model sudoku problems as CNF formulae and solve them
 * with the sat solver
 * The constructor can be given a set of fixed field assignments with both
 * x and y indices in [1,9]]
 */
class Sudoku(fixedVars:Array<Array<Int>>) : ClauseSetWatchedLiterals(makeSudokuFormula(fixedVars))
{
    //TODO string based constructor or from a file
    fun printTrueAssignments()
    {
        for (vari in this.getPresentVariables()) {
            if (!vari.isUnset && vari.boolSetting!!) {
                println(vari.id)
            }
        }
    }

    companion object {
        fun makeVarId(x: Int, y: Int, assignment: Int): String =
                (x.toString() + "x" + y.toString() + ":" + assignment.toString())

        fun makeSudokuFormula(fixedVars: Array<Array<Int>>): Array<ClauseWatchedLiterals> {
            val vars: SudokuVariableSet = makeVariables()
            //base sudoku rules can be explained with two rules
            //R1a + R1b: Every field must have exactly one assignment
            // (split into R1a"at least one assignment" and R1b"at most one assignment"
            //R2: Every block/column/row must contain every assignment
            return (ensureFieldsHaveSomeAssignment(vars) +
                    ensureFieldsHaveAtMostOneAssignment(vars) +
                    ensureBlocksHaveEveryAssignment(vars) +
                    ensureBlocksHaveUniqueAssignments(vars) +
                    fixAssignments(fixedVars,vars)
                    ).toTypedArray()
        }

        private fun fixAssignments(fixedVars: Array<Array<Int>>,knownVars:SudokuVariableSet): Iterable<ClauseWatchedLiterals> {
            val retu = mutableListOf<ClauseWatchedLiterals>()
            for (fix in fixedVars) {
                assert(fix.size == 3)
                    { "Assignments must have 3 numbers between 1 and 9" }
                fix.forEach { assert(it in 1..9)
                    { "Assignments must be between 1 and 9" }
                }
                //values are given as [1..9]
                val theVar = knownVars[fix[0]-1][fix[1]-1][fix[2]-1]
                retu.add(ClauseWatchedLiterals(Literal(theVar,true)))
            }
            return retu
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
                                    yield(Variable(Sudoku.makeVarId(x, y, b)))
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

        private fun ensureFieldsHaveSomeAssignment(vars: SudokuVariableSet): Iterable<ClauseWatchedLiterals> =
                sequence {
                    for (x in 0..8) {
                        for (y in 0..8) {
                            val thisFieldsAssignments: Array<Literal> = vars[x][y].map { Literal(it, true) }.toTypedArray()
                            val anyOfThem = ClauseWatchedLiterals(thisFieldsAssignments)
                            yield(anyOfThem)
                        }
                    }
                }.toList()


        private fun ensureFieldsHaveAtMostOneAssignment(vars: SudokuVariableSet): Iterable<ClauseWatchedLiterals> =
                sequence {
                    for (x in 0..8) {
                        for (y in 0..8) {
                            for (i in 0..8) {
                                for (j in (0..8)) {
                                    if (i == j)
                                        continue
                                    val curRule = ClauseWatchedLiterals(arrayOf(
                                            Literal(vars[x][y][i], false),
                                            Literal(vars[x][y][j], false)
                                    ))
                                    yield(curRule)

                                }
                            }
                        }
                    }
                }.toList()


        private fun ensureBlocksHaveEveryAssignment(vars: SudokuVariableSet): Iterable<ClauseWatchedLiterals> {
            val retu: MutableList<ClauseWatchedLiterals> = mutableListOf()
            for (assignment in 0..8) {
                //rows
                for (x in 0..8) {
                    //in row x, any field must have 'assignment'
                    val curRule = ClauseWatchedLiterals(arrayOf(
                            Literal(vars[x][0][assignment], true),
                            Literal(vars[x][1][assignment], true),
                            Literal(vars[x][2][assignment], true),
                            Literal(vars[x][3][assignment], true),
                            Literal(vars[x][4][assignment], true),
                            Literal(vars[x][5][assignment], true),
                            Literal(vars[x][6][assignment], true),
                            Literal(vars[x][7][assignment], true),
                            Literal(vars[x][8][assignment], true),
                    ))
                    retu.add(curRule)
                }

                //columns
                for (y in 0..8) {
                    //in column y, any field must have 'assignment'
                    val curRule = ClauseWatchedLiterals(arrayOf(
                            Literal(vars[0][y][assignment], true),
                            Literal(vars[1][y][assignment], true),
                            Literal(vars[2][y][assignment], true),
                            Literal(vars[3][y][assignment], true),
                            Literal(vars[4][y][assignment], true),
                            Literal(vars[5][y][assignment], true),
                            Literal(vars[6][y][assignment], true),
                            Literal(vars[7][y][assignment], true),
                            Literal(vars[8][y][assignment], true),
                    ))
                    retu.add(curRule)
                }

                //blocks
                for (xb in 0..2) {
                    for (yb in 0..2) {
                        val xc = xb * 3
                        val yc = yb * 3
                        val curRule = ClauseWatchedLiterals(arrayOf(
                                Literal(vars[xc][yc][assignment], true),
                                Literal(vars[xc][yc + 1][assignment], true),
                                Literal(vars[xc][yc + 2][assignment], true),
                                Literal(vars[xc + 1][yc][assignment], true),
                                Literal(vars[xc + 1][yc + 1][assignment], true),
                                Literal(vars[xc + 1][yc + 2][assignment], true),
                                Literal(vars[xc + 2][yc][assignment], true),
                                Literal(vars[xc + 2][yc + 1][assignment], true),
                                Literal(vars[xc + 2][yc + 2][assignment], true),
                        ))
                        retu.add(curRule)
                    }
                }
            }
            return retu
        }


        fun ensureBlocksHaveUniqueAssignments(vars: SudokuVariableSet): Iterable<ClauseWatchedLiterals> {
            val retu: MutableList<ClauseWatchedLiterals> = mutableListOf()
            for (curRow in 0..8) {
                for (rowsField in 0..8) {
                    for (rowsOtherField in 0..8) {
                        if (rowsOtherField == rowsField) {
                            continue
                        }
                        for (assignment in 0..8) {
                            //row
                            retu.add(ClauseWatchedLiterals(arrayOf(
                                    Literal(vars[curRow][rowsField][assignment], false),
                                    Literal(vars[curRow][rowsOtherField][assignment], false)
                            )))
                            //column
                            retu.add(ClauseWatchedLiterals(arrayOf(
                                    Literal(vars[rowsField][curRow][assignment], false),
                                    Literal(vars[rowsOtherField][curRow][assignment], false)
                            )))
                        }
                    }
                }
            }

            //blocks
            for (bx in 0..2) {
                for (by in 0..2) {
                    for (dx in 0..2) {
                        for (odx in 0..2) {
                            if (dx == odx) continue
                            for (dy in 0..2) {
                                for (ody in 0..2) {
                                    val x = bx * 3 + dx
                                    val y = by * 3 + dy
                                    val otherX = bx * 3 + odx
                                    val otherY = by * 3 + ody
                                    for (assignment in 0..8) {
                                        retu.add(ClauseWatchedLiterals(arrayOf(
                                                Literal(vars[x][y][assignment], false),
                                                Literal(vars[otherX][otherY][assignment], false)
                                        )))
                                    }
                                }
                            }
                        }
                    }
                }
            }
            return retu
        }
    }
}





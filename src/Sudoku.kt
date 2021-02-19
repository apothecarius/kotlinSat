import org.junit.Test
import kotlin.test.assertEquals

typealias SudokuVariableSet = Array<Array<Array<Variable>>>
/**
 * This class serves to model sudoku problems as CNF formulae and solve them with the sat solver
 */
class Sudoku : ClauseSetWatchedLiterals(makeBaseFormula()) {

    fun fixVar(x:Int, y:Int, option:Int)
    {
        assert((1..9).contains(x))
        assert((1..9).contains(y))
        assert((1..9).contains(option))

        this.findVariable(makeVarId(x,y,option))!!.setTo(true)
    }

    fun printTrueAssignments()
    {
        for (vari in this.getPresentVariables()) {
            if (!vari.isUnset && vari.boolSetting!!) {
                println(vari.id)
            }
        }
    }

    companion object {
        fun makeVarId(x:Int,y:Int,assignment:Int):String =
                (x.toString() + "x" + y.toString() + ":" + assignment.toString())
        public fun makeBaseFormula(): Array<ClauseWatchedLiterals> {
            val vars: SudokuVariableSet = makeVariables()
            //base sudoku rules can be explained with two rules
            //R1a + R1b: Every field must have exactly one assignment
            // (split into R1a"at least one assignment" and R1b"at most one assignment"
            //R2: Every block/column/row must contain every assignment
            return (ensureFieldsHaveSomeAssignment(vars) +
                    ensureFieldsHaveAtMostOneAssignment(vars) +
                    ensureBlocksHaveEveryAssignment(vars)).toTypedArray()
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
                                    yield(Variable(Sudoku.makeVarId(x,y,b)))
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
                    for (x in 0..8)
                    {
                        for (y in 0..8)
                        {
                            for (i in 0..8)
                            {
                                for (j in (0..8))
                                {
                                    if(i == j)
                                        continue
                                    val curRule = ClauseWatchedLiterals(arrayOf(
                                            Literal(vars[x][y][i],false),
                                            Literal(vars[x][y][j],false)
                                    ))
                                    yield(curRule)

                                }
                            }
                        }
                    }
                }.toList()



        private fun ensureBlocksHaveEveryAssignment(vars: SudokuVariableSet): Iterable<ClauseWatchedLiterals>
        {
            val retu:MutableList<ClauseWatchedLiterals> = mutableListOf()
            for(assignment in 0..8)
            {
                //rows
                for(x in 0..8)
                {
                    //in row x, any field must have 'assignment'
                    val curRule = ClauseWatchedLiterals(arrayOf(
                            Literal(vars[x][0][assignment],true),
                            Literal(vars[x][1][assignment],true),
                            Literal(vars[x][2][assignment],true),
                            Literal(vars[x][3][assignment],true),
                            Literal(vars[x][4][assignment],true),
                            Literal(vars[x][5][assignment],true),
                            Literal(vars[x][6][assignment],true),
                            Literal(vars[x][7][assignment],true),
                            Literal(vars[x][8][assignment],true),
                    ))
                    retu.add(curRule)
                }

                //columns
                for(y in 0..8)
                {
                    //in column y, any field must have 'assignment'
                    val curRule = ClauseWatchedLiterals(arrayOf(
                            Literal(vars[0][y][assignment],true),
                            Literal(vars[1][y][assignment],true),
                            Literal(vars[2][y][assignment],true),
                            Literal(vars[3][y][assignment],true),
                            Literal(vars[4][y][assignment],true),
                            Literal(vars[5][y][assignment],true),
                            Literal(vars[6][y][assignment],true),
                            Literal(vars[7][y][assignment],true),
                            Literal(vars[8][y][assignment],true),
                    ))
                    retu.add(curRule)
                }

                //blocks
                for(xb in 0..2)
                {
                    for(yb in 0..2)
                    {
                        val xc = xb*3
                        val yc = yb*3
                        val curRule = ClauseWatchedLiterals(arrayOf(
                                Literal(vars[xc][yc][assignment],true),
                                Literal(vars[xc][yc+1][assignment],true),
                                Literal(vars[xc][yc+2][assignment],true),
                                Literal(vars[xc+1][yc][assignment],true),
                                Literal(vars[xc+1][yc+1][assignment],true),
                                Literal(vars[xc+1][yc+2][assignment],true),
                                Literal(vars[xc+2][yc][assignment],true),
                                Literal(vars[xc+2][yc+1][assignment],true),
                                Literal(vars[xc+2][yc+2][assignment],true),
                        ))
                        retu.add(curRule)
                    }
                }
            }
            return retu
        }
    }


    @Test
    fun variableCreatorTest()
    {
        //ensure sizes, which the function does intself
        val vars = Sudoku.makeVariables()
    }

    @Test
    fun rule1aTest()
    {
        val vars = makeVariables()
        val r1a = ensureFieldsHaveSomeAssignment(vars)
        assertEquals(81,r1a.count())

        //TODO verify that this actually prohibits certain assignments
    }

    @Test
    fun rule1bTest()
    {
        val vars = makeVariables()
        val r1b = ensureFieldsHaveAtMostOneAssignment(vars)
        assertEquals(9*9*9*8,r1b.count())//might be fewer



    }

    @Test
    fun rule2Test()
    {
        val vars = makeVariables()
        val r2 = ensureBlocksHaveEveryAssignment(vars)
        assertEquals(3*9*9,r2.count())



    }


    @Test
    fun solveTest()
    {
        val sudo = Sudoku()
        sudo.let{
            fixVar(1,1,5)
            fixVar(1,3,9)
            fixVar(1,7,4)
            fixVar(2,1,7)
            fixVar(2,3,8)
            fixVar(2,4,3)
            fixVar(2,6,4)
            fixVar(2,7,9)
            fixVar(3,1,6)
            fixVar(3,3,1)
            fixVar(3,7,7)
            fixVar(3,8,3)
            fixVar(4,1,4)
            fixVar(4,2,6)
            fixVar(4,3,2)
            fixVar(4,4,5)
            fixVar(5,1,3)
            fixVar(5,2,8)
            fixVar(5,3,5)
            fixVar(5,4,7)
            fixVar(5,5,2)
            fixVar(5,7,6)
            fixVar(5,8,4)
            fixVar(5,9,9)
            fixVar(6,1,1)
            fixVar(6,3,7)
            fixVar(6,4,4)
            fixVar(6,6,8)
            fixVar(6,7,2)
            fixVar(7,1,2)
            fixVar(7,4,1)
            fixVar(7,9,4)
            fixVar(8,3,3)
            fixVar(8,5,4)
            fixVar(8,8,8)
            fixVar(8,9,7)
            fixVar(9,2,7)
            fixVar(9,5,5)
            fixVar(9,6,3)
            fixVar(9,9,6)

        }
        cdclSAT(sudo)
        sudo.printTrueAssignments()

    }
}





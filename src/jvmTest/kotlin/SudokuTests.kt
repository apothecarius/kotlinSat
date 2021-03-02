package test

import algorithms.Sudoku
import org.junit.Test
import kotlin.test.assertEquals
import kotlin.test.assertTrue

class SudokuTests {

    @Test
    fun quickSudokuSetupTest()
    {
        val puzzle:String =
            " 3|" +
            "   195|" +
            "  8    6|" +
            "8   6|"+
            "4  8    1|" +
            "    2|" +
            " 6    28|" +
            "   419  5|"+
            "       7|"
        val sudo = Sudoku(puzzle)
        assertTrue { verifySudokuVariableCount(sudo) }
        val solvable = sudo.solve()
        assertEquals(true,sudo.findVariable("2x1:3")!!.boolSetting)
        assertTrue { solvable }
        verifySudokuSum(sudo.to9By9Array())
        sudo.print()
        //TODO check that solution contains original assignments
    }

    @Test
    fun emptySudokuTest()
    {
        //should just generate some sudoku if no constraints are given
        val sudo = Sudoku(arrayOf())
        assertTrue { verifySudokuVariableCount(sudo) }
        val solvable = sudo.solve()
        val solution = sudo.to9By9Array()
        verifySudokuSum(solution)

        assertTrue { solvable }
    }

    private fun verifySudokuVariableCount(sudo: Sudoku):Boolean
    {
        return sudo.getPresentVariables().toList().size == 9*9*9
    }

    @Test
    fun someSudokuTest()
    {
        val fixes = arrayOf(
            Triple(1, 1, 5),
            Triple(1, 3, 9),
            Triple(1, 7, 4),
            Triple(2, 1, 7),
            Triple(2, 3, 8),
            Triple(2, 4, 3),
            Triple(2, 6, 4),
            Triple(2, 7, 9),
            Triple(3, 1, 6),
            Triple(3, 3, 1),
            Triple(3, 7, 7),
            Triple(3, 8, 3),
            Triple(4, 1, 4),
            Triple(4, 2, 6),
            Triple(4, 3, 2),
            Triple(4, 4, 5),
            Triple(5, 1, 3),
            Triple(5, 2, 8),
            Triple(5, 3, 5),
            Triple(5, 4, 7),
            Triple(5, 5, 2),
            Triple(5, 7, 6),
            Triple(5, 8, 4),
            Triple(5, 9, 9),
            Triple(6, 1, 1),
            Triple(6, 3, 7),
            Triple(6, 4, 4),
            Triple(6, 6, 8),
            Triple(6, 7, 2),
            Triple(7, 1, 2),
            Triple(7, 4, 1),
            Triple(7, 9, 4),
            Triple(8, 3, 3),
            Triple(8, 5, 4),
            Triple(8, 8, 8),
            Triple(8, 9, 7),
            Triple(9, 2, 7),
            Triple(9, 5, 5),
            Triple(9, 6, 3),
            Triple(9, 9, 6)
        )

        val sudo = Sudoku(fixes)

        assertTrue { verifySudokuVariableCount(sudo) }
        val issatisfiable = sudo.solve()
        assertTrue { issatisfiable }

        val solution = sudo.to9By9Array()
        verifySudokuSum(solution)
        //verify that constraints are part of the solution
        for (fixation in fixes) {
            assertEquals(fixation.third, solution[fixation.first-1][fixation.second-1])
        }
        //TODO verify sudoku conditions. Iterate over true assigned vars by coordinate
        // and verify that each row block and column has exactly one of each assignments
    }

    /**
     * Iterates over columns, lines and cubes and asserts that the sum over the assignments is right (45)
     */
    private fun verifySudokuSum(sudo:Array<Array<Int>>)
    {
        assertEquals(9,sudo.size)
        sudo.forEach { assertEquals(9,it.size) }

        for(blockType in 1..3) {
            for (blkIdx in 0..8) {
                var sum = 0
                for (fieldIdx in 0..8)
                {
                    val (x,y) = Sudoku.getSudokuFieldCoord(blkIdx,fieldIdx,blockType)
                    sum += sudo[x][y]
                }


                assertEquals(45, sum)
            }
        }


    }
}
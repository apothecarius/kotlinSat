package test

import algorithms.Backbone
import algorithms.cdclSAT
import materials.ClauseSetWatchedLiterals
import materials.Literal
import materials.predicate
import org.junit.Test
import support.readCnf
import kotlin.test.assertEquals
import kotlin.test.assertFalse
import kotlin.test.assertTrue

class CnfFormulaTests {


    @Test
    fun refinedEssentialsTest()
    {
        //testrun with file from SAT Competition
        //this file takes impractically long to solve without VSIDS
        val form: ClauseSetWatchedLiterals = readCnf("probFiles/fla-qhid-200-1.cnf")
        assertTrue(cdclSAT(form))
    }




    @Test
    fun bombTest()
    {
        val formula = readCnf("probFiles/smallSatBomb.cnf")
        val backbone = Backbone.getBackboneIntersections(formula)
        val expectedBackbone:List<Int> = listOf(-215, -205, 131, 138, 143, 204, 208, 210 ,243)
        assertEquals(9,backbone.size)
        for (lit: Literal in backbone) {
            val asInt = lit.first.id.toInt() * if(lit.predicate) 1 else -1
            assertTrue(expectedBackbone.contains(asInt))
        }
    }



    @Test
    fun cnfReadTest()
    {
        val formula = readCnf("probFiles/smallSatBomb.cnf")
        assertTrue(formula.isFresh)
        assertEquals(formula.getClauses().size, 1250)
        assertEquals(formula.getPresentVariables().count(),209)

        //TODO satisfiability check should return true, but takes forever without VSIDS
        //the correct backbone is also noted
    }

    @Test
    fun unLittleSatTest()
    {
        //read a small unsat formula and verify UNSAT
        val formula = readCnf("probFiles/unLittleSat.cnf")
        assertTrue(formula.isFresh)
        assertFalse(cdclSAT(formula))
    }

    @Test
    fun littleSatTest()
    {
        val formula = readCnf("probFiles/littleSat.cnf")
        assertTrue(formula.isFresh)
        assertTrue(cdclSAT(formula))
    }

}
package test

import algorithms.Backbone
import algorithms.cdclSAT
import materials.*
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
        assertFormulaInvariances(form)
        assertTrue(cdclSAT(form))

        assertFormulaInvariances(form)
    }

    companion object
    {
        /**
         * Should verify some internal constraints by checking the formula in all of
         * these unit tests after running CDCL or even after setting up the formula
         */
        internal fun assertFormulaInvariances(form:ClauseSet)
        {
            //verify that variable objects were not duplicated (pointer equality
            // if there is .id equality)
            val idToVar:MutableMap<String, Variable> = mutableMapOf()
            for (clause in form.getClauses()) {
                for (lit in clause.literals) {
                    val itsId = lit.variable.id
                    if (idToVar.containsKey(itsId)) {
                        assertEquals(lit.variable, idToVar[itsId])
                    } else {
                        idToVar[itsId] = lit.variable
                    }
                }
            }

            //verify that var2clauses is completely correct
            assertEquals(idToVar.size,form.getOccurencesLookup().size) //both should count the number of variables
            for((curVar,occurences) in form.getOccurencesLookup())
            {
                assertTrue(occurences.all { occu -> occu.literals.any { lit -> curVar == lit.variable } })
            }
        }
    }



    @Test
    fun bombTest()
    {
        val formula = readCnf("probFiles/smallSatBomb.cnf")
        assertFormulaInvariances(formula)
        val backbone = Backbone.getBackboneIntersections(formula)
        assertFormulaInvariances(formula)
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
        assertFormulaInvariances(formula)
        assertTrue(formula.isFresh)
        assertEquals(formula.getClauses().size, 1250)
        assertEquals(formula.getPresentVariables().count(),209)
        assertTrue(cdclSAT(formula))
    }

    @Test
    fun unLittleSatTest()
    {
        //read a small unsat formula and verify UNSAT
        val formula = readCnf("probFiles/unLittleSat.cnf")
        assertFormulaInvariances(formula)
        assertTrue(formula.isFresh)
        assertFalse(cdclSAT(formula))
    }

    @Test
    fun littleSatTest()
    {
        val formula = readCnf("probFiles/littleSat.cnf")
        assertFormulaInvariances(formula)
        assertTrue(formula.isFresh)
        assertTrue(cdclSAT(formula))
    }

}
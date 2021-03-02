package test

import materials.ClauseSet
import materials.ClauseSetWatchedLiterals
import materials.Literal
import algorithms.*
import materials.Variable
import materials.VariableIdentifier
import materials.VariableSetting
import materials.makeVarIds
import kotlin.test.Test
import kotlin.test.*
import materials.predicate
import materials.variable
import support.Either
import support.Helpers
import support.readCnf
import kotlin.random.Random

/**
 * create random clausesets and compare the result of DPLL and CDCL solvers
 *
 */

class Tests{
    /**
     * Verifies that all solvers agree on whether they can find a model for any formula or not
     */
    @Test
    fun testSolvers() = testSolvers(numTests = 100,numVars = 25,numClauses= 120,varStep = 10)

    private fun testSolvers(numTests:Int,numVars:Int,numClauses:Int,varStep:Int) {
        assertTrue(numVars < 26)


        val knownVars:List<VariableIdentifier> = makeVarIds(numVars)

        for (_iter:Int in 1..numTests) {
            val boolCode:String = makeBoolCode(knownVars,numClauses, varStep)

            val curClauseSetDpll = ClauseSet(boolCode)
            val curClauseSetCdcl = ClauseSet(boolCode)//materials.ClauseSetWatchedLiterals(boolCode)
            val watchedLiteralClauseSet = ClauseSetWatchedLiterals(boolCode)
            val dpllResult:Boolean = dpllSAT(curClauseSetDpll)
            val cdclResult:Boolean = cdclSAT(curClauseSetCdcl)
            val watchedLiteralTable: CdclTable = cdclSolve(watchedLiteralClauseSet)
            val watchedLiteralResult:Boolean = watchedLiteralClauseSet.isFulfilled

            val fail:Boolean = (dpllResult != cdclResult || dpllResult != watchedLiteralResult)
            assertFalse(fail)

            if (cdclResult)
            {
                //if formula is satisfied, then it must also be an implicant
                //test that while we're here
                val isImplicant = Implicant.isImplicant(curClauseSetCdcl)
                assertTrue(isImplicant)


                //val cdclCopyTable:CdclTable = cdclSolve(watchedLiteralClauseSet)
                val piNonWl = Implicant.getPrimeImplicant(curClauseSetCdcl)
                val piWithWl = Implicant.getPrimeImplicantWithWatchedLiterals(watchedLiteralClauseSet, watchedLiteralTable)


                val clWithPI = arrayOf(curClauseSetCdcl,watchedLiteralClauseSet)
                //clear all materials.getVariable settings
                clWithPI.forEach {clp ->  clp.getPresentVariables().forEach {cv -> cv.unset() }}
                //apply materials.getVariable setting to primeImplicant
                arrayOf(piNonWl, piWithWl).forEach { it.forEach{lit: Literal -> lit.first.setTo(lit.second)} }
                //verify, that result is indeed primeImplicant
                assertFalse(clWithPI.any { Implicant.getNonPrimeImplicantVariable(it).let{ freeVar ->
                            freeVar is Either.Left && freeVar.value != null}},
                    "ERROR: Prematurely returned PrimeImplicant")
            }
        }
    }


    private fun makeBoolCode(numVars: Int, numClauses: Int, varStep: Int):String {
        return makeBoolCode(makeVarIds(numVars), numClauses, varStep)
    }
    private fun makeBoolCode(knownVars:List<VariableIdentifier>, numClauses:Int, varStep:Int): String {
        val clauseList:MutableList<String> = mutableListOf()
        for (clauseIter: Int in 1..numClauses) {
            val varList:MutableList<String> = mutableListOf()
            var varsIter:Int = 0
            while(true) {
                varsIter += Math.abs(Random.nextInt() % varStep)+1
                if (varsIter >= knownVars.size) {
                    break
                } else {
                    var s:String =
                            if (Random.nextBoolean()) "!" else ""

                    s += knownVars[varsIter]
                    varList.add(s)
                }
            }
            if(!varList.isEmpty())
                clauseList.add(varList.joinToString(separator="|"))
        }
        return clauseList.joinToString(separator = " & ")
    }


    fun isLiteralSetDifferent(setA:List<Literal>, setB:List<Literal>):Boolean
    {
        if (setA.size != setB.size) {
            return true
        }
        val itA = setA.iterator()
        val itB = setB.iterator()

        while (itA.hasNext()) {
            assert(itB.hasNext())
            var a: Literal = itA.next()
            var b: Literal = itB.next()
            if (a.variable.id != b.variable.id) {
                return true
            }
            if (a.predicate != b.predicate) {
                return true
            }
        }
        return false
    }


    private fun ClauseSet.countSetVars():Int = this.getPresentVariables().count{ !it.isUnset }

    fun implicantTest1()
    {
        //fehlerfall 1: mit WL hat ein unnötiges literal
        val fehlerKlausCode = "!C|!E & !B|D & !B|D|!E & B|C|D & !B|!D & !C|!E & C|!D & C"
        val fehlerKlaus1 = ClauseSetWatchedLiterals(fehlerKlausCode)
        val fehlerKlaus2 = ClauseSetWatchedLiterals(fehlerKlausCode)
        cdclSAT(fehlerKlaus1)
        println(Implicant.getPrimeImplicant(fehlerKlaus1))
        println(Implicant.getPrimeImplicantWithWatchedLiterals(fehlerKlaus2))

        println(fehlerKlaus1.countSetVars())
        println(fehlerKlaus2.countSetVars())
    }

    fun implicantTest2()
    {
        val fehlerKlausCode = "E & B|E & B|!D & B|D|E & !D|E"
        //fehler: solver setzt !B, aber !B existiert hier nicht, primplikantenalgo sollte trotzdem b unsetten
        val fehlerKlaus1 = ClauseSetWatchedLiterals(fehlerKlausCode);
        val fehlerKlaus2 = ClauseSetWatchedLiterals(fehlerKlausCode);
        cdclSAT(fehlerKlaus1)

        println(Implicant.getPrimeImplicant(fehlerKlaus1))
        println(Implicant.getPrimeImplicantWithWatchedLiterals(fehlerKlaus2))

        println(fehlerKlaus1.countSetVars())
        println(fehlerKlaus2.countSetVars())
    }
    fun implicantTest3()
    {
        val fehlerKlausCode = "B|!C|!D|E & C|!E & !C|!D|!E & !B|!C|E & !C|!E & !B|D|E & C|E & C"

        val fehlerKlaus1 = ClauseSetWatchedLiterals(fehlerKlausCode);
        val fehlerKlaus2 = ClauseSetWatchedLiterals(fehlerKlausCode);
        val fehlerKlaus3 = ClauseSet(fehlerKlausCode)

        cdclSAT(fehlerKlaus1)
        fehlerKlaus1.printVarSettings()
        println(Implicant.getPrimeImplicant(fehlerKlaus1))
        println()

        val table = cdclSolve(fehlerKlaus2)
        fehlerKlaus2.printVarSettings()
        println(Implicant.getPrimeImplicantWithWatchedLiterals(fehlerKlaus2, table))
        println()

        val table3 = cdclSolve(fehlerKlaus3)
        fehlerKlaus3.printVarSettings()
        println(Implicant.getPrimeImplicant(fehlerKlaus3))
    }


    fun implicantTest4()
    {
        val fehlerKlausCode = "C|!G & D|!F|I & !C|I & !F|G|K & G & D|!I & !E|!J|K & !D|!E|I|J & C|!G|H|I|K & B|D|!F|!I|!J & !B|H|I & C|!I|!J"
        //val fehlerKlausCode = "!B|!D|!E & B|D & C|E & C|!E & !B|D & C|!D & !B|C|!E"

        val fehlerKlaus1 = ClauseSetWatchedLiterals(fehlerKlausCode);
        val fehlerKlaus2 = ClauseSetWatchedLiterals(fehlerKlausCode);
        val fehlerKlaus3 = ClauseSet(fehlerKlausCode)

        cdclSAT(fehlerKlaus1)
        fehlerKlaus1.printVarSettings()
        println(Implicant.getPrimeImplicant(fehlerKlaus1))
        println()

        val table = cdclSolve(fehlerKlaus2)
        fehlerKlaus2.printVarSettings()
        println(Implicant.getPrimeImplicantWithWatchedLiterals(fehlerKlaus2, table))
        println()

        val table3 = cdclSolve(fehlerKlaus3)
        fehlerKlaus3.printVarSettings()
        println(Implicant.getPrimeImplicant(fehlerKlaus3))
    }

    @Test
    fun testBackbone():Unit
    {
        val fa = ClauseSetWatchedLiterals("a & a|b|c")
        val bba = Backbone.getBackboneKaiKue(fa)//has backbone of A
        var success:Boolean = bba.size == 1 && bba.contains(Literal(fa.findVariable("a")!!, true))
        assertTrue(success)

        val fb = ClauseSetWatchedLiterals("!a & a|b")
        val bbb = Backbone.getBackboneKaiKue(fb)// has backbone of !a,b
        success = bbb.size == 2 && bbb.contains(Literal(fb.findVariable("a")!!, false)) &&
                bbb.contains(Literal(fb.findVariable("b")!!, true))
        assertTrue(success)

        val fc = ClauseSetWatchedLiterals("D|!G|!J & D|!I|J & F|!J|!K & F|I & !F|!J & B|!F|!I & F|!J & D|!G & !F|G & !F|!G & !F|!J & !D|!F|!G|!K & !F|!G|K & M|N")
        val bbc = Backbone.getBackboneKaiKue(fc)//has a backbone of [(D, true), (F, false), (I, true), (J, false)]
        success = bbc.size == 4 && bbc.contains(Literal(fc.findVariable("D")!!, true)) &&
                bbc.contains(Literal(fc.findVariable("F")!!, false)) &&
                bbc.contains(Literal(fc.findVariable("I")!!, true)) &&
                bbc.contains(Literal(fc.findVariable("J")!!, false))
        assertTrue(success)




    }

    fun testBackboneStocha() {
        val randy:Random = Random(1253132)
        val knownVars = makeVarIds(8)

        for (i in 0..100) {
            var boolCode:String = makeBoolCode(knownVars,10, 4)
            val klaus = ClauseSetWatchedLiterals(boolCode)

            println("Finding backbone for formula: ")
            println(klaus)
            val bb = Backbone.getBackboneKaiKue(klaus, false)
            val bbc = Backbone.getBackboneKaiKue(klaus, true)
            if (bb != bbc) {
                println("mismatch in solver optimization")
                println("With optimization: "+bbc)
                println("Without optimization:" +bb)
            }
            if (bb.isEmpty()) {
                println("backbones are empty")
                println()
                continue
            }

            println(bb)
            println()
        }

    }

    @Test
    fun testImplicantOld()
    {
        val k = ClauseSet("a & b|c")
        val varA: Variable = k.getPresentVariables().find { it.id == "a" }!!
        val varB: Variable =k.getPresentVariables().find { it.id == "b" }!!
        val varC: Variable =k.getPresentVariables().find { it.id == "c" }!!

        varA.setTo(VariableSetting.True)
        assertFalse( k.isFulfilled)
        assertFalse( k.isEmpty)
        assertFalse(Implicant.isImplicant(k))
        assertFalse(Implicant.isPrimeImplicant(k))

        varB.setTo(true)
        assertTrue(k.isFulfilled)
        assertTrue(Implicant.isImplicant(k))
        assertTrue(Implicant.isPrimeImplicant(k))

        varC.setTo(true)
        assertTrue(Implicant.isImplicant(k))
        assertTrue(!Implicant.isPrimeImplicant(k))

        varC.setTo(false)
        assertTrue(Implicant.isImplicant(k))
        assertTrue(!Implicant.isPrimeImplicant(k))

        return
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


    fun timingTests(): Unit {
        val cod = makeBoolCode(4000,5000,2900)
        var cs = ClauseSet(cod)
        var cswl = ClauseSetWatchedLiterals(cod)
        val start1 = System.currentTimeMillis()
        val erg1 = cdclSolve(cs)
        val end1 = System.currentTimeMillis()
        val start2 = System.currentTimeMillis()
        val erg2 = cdclSolve(cswl)
        val end2 = System.currentTimeMillis()

        val startSplit = System.currentTimeMillis()
        val splitting = cs.separateClauses()
        val endSplit = System.currentTimeMillis()
        println(endSplit - startSplit)
        println(splitting.size)
        for (s in splitting) {
            println(s)
        }

        println(cod)
        println(end1 - start1)
        println(end2 - start2)

        println(cs.isFulfilled)
        println(cswl.isFulfilled)
    }

    @Test
    fun unsatTest()
    {
        //not satisfiable because !C -> !B, but C|B
        val code = "C|B & !A & !C & C|!A|!B & C|!B"
        assertFalse(cdclSAT(code))
    }

    @Test
    fun axiomaticEntriesTest()
    {
        val bb2 = ClauseSetWatchedLiterals("!a & a|b")
        val axiom = cdclSolve(bb2).getAxiomaticEntries()
        assertEquals(axiom.count(),2)
    }

    @Test
    fun testToStringReflexivity()
    {
        val code = "a|b & !b|c & c|!d"
        val formula = ClauseSet(code)
        val formulaWl = ClauseSetWatchedLiterals(code)

        assertEquals(code,formula.toString())
        assertEquals(code,formulaWl.toString())
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
    fun testQuickBackbone()
    {
        val numTests = 40
        val numVars = 30
        val numClauses = 100
        val varStep = 16


        val knownVars = makeVarIds(numVars)
        var numFails = 0
        var runTests = 0

        var sumMsecKaiKueSlow = 0
        var sumMsecKaiKueFast = 0
        var sumMsecIntersect = 0

        var numKaiKueRuns = 0
        var numIntersectRuns = 0

        for (_iter:Int in 1..numTests) {
            val code:String = makeBoolCode(knownVars,numClauses,varStep)

            if (cdclSAT(ClauseSetWatchedLiterals(code)))
            {
                runTests++

                val t1 = System.currentTimeMillis()
                val kaiKueSlow: Set<Literal> = Backbone.getBackboneKaiKue(ClauseSetWatchedLiterals(code), false)
                val kaiKueSlowRuns = algorithms.Backbone.numCdclRuns
                val t2 = System.currentTimeMillis()

                val t3 = System.currentTimeMillis()
                val kaiKue: Set<Literal> = Backbone.getBackboneKaiKue(ClauseSetWatchedLiterals(code))
                val kaiKueRuns = Backbone.numCdclRuns
                val t4 = System.currentTimeMillis()
                val t5 = System.currentTimeMillis()
                val inters: Set<Literal> = Backbone.getBackboneIntersections(ClauseSetWatchedLiterals(code))
                val intersRuns = Backbone.numCdclRuns
                val t6 = System.currentTimeMillis()

                sumMsecKaiKueSlow += (t2-t1).toInt()
                sumMsecKaiKueFast += (t4-t3).toInt()
                sumMsecIntersect += (t6-t5).toInt()
                numKaiKueRuns += kaiKueRuns
                numIntersectRuns += intersRuns

                val failure:Boolean = isLiteralSetDifferent(inters.toList().sortedBy { it.variable.id },
                        kaiKue.toList().sortedBy { it.variable.id })
                assertFalse(failure)
                if (failure) {
                    numFails++
                    println(code)
                    println(inters)
                }
            }
        }
    }
    @Test
    fun activityInitializationTest()
    {
        val form: ClauseSetWatchedLiterals = ClauseSetWatchedLiterals("a|b|c & b|!a & !c|a | d")
        for (vari: Variable in form.getPresentVariables()) {
            assertEquals(when(vari.id){
                "a" -> 3f
                "b" -> 2f
                "c" -> 2f
                "d" -> 1f
                else -> {
                    fail()
                    0f
                }
            },vari.activity)
        }
    }

    @Test
    fun charDigitToIntTest()
    {
        for(i in 0..9)
        {
            val asChar:Char = i.toString()[0]
            assertEquals(i,Helpers.digitToInt(asChar))
        }
        assertFails { Helpers.digitToInt('a') }
        assertFails { Helpers.digitToInt('-') }
        assertFails { Helpers.digitToInt('ü') }

    }

    @Test
    fun refinedEssentialsTest()
    {
        //testrun with file from SAT Competition
        //this file takes impractically long to solve without VSIDS
        val form: ClauseSetWatchedLiterals = readCnf("probFiles/fla-qhid-200-1.cnf")
        assertTrue(cdclSAT(form))
    }
}


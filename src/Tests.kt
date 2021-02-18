import org.junit.Assert.assertFalse
import org.junit.Assert.assertTrue
import org.junit.Test
import java.util.*
import java.util.stream.IntStream
import kotlin.test.assertEquals

/**
 * create random clausesets and compare the result of DPLL and CDCL solvers
 *
 */

class Tests{
    @Test
    fun testSolvers() = testSolvers(numTests = 100,numVars = 25,numClauses= 120,varStep = 10)

    fun testSolvers(numTests:Int,numVars:Int,numClauses:Int,varStep:Int) {
        assert(numVars < 26)

        val randy: Random = Random()

        val knownVars:List<VariableIdentifier> = makeVarIds(numVars)

        for (_iter:Int in 1..numTests) {
            var boolCode:String = makeBoolCode(randy,knownVars,numClauses, varStep)
            if (verbose) {
                println(boolCode)
            }

            val curClauseSetDpll = ClauseSet(boolCode)
            val curClauseSetCdcl = ClauseSet(boolCode)//ClauseSetWatchedLiterals(boolCode)
            val watchedLiteralClauseSet = ClauseSetWatchedLiterals(boolCode)
            val dpllResult:Boolean = dpllSAT(curClauseSetDpll)
            val cdclResult:Boolean = cdclSAT(curClauseSetCdcl)
            val watchedLiteralTable:CdclTable = cdclSolve(watchedLiteralClauseSet)
            val watchedLiteralResult:Boolean = watchedLiteralClauseSet.isFulfilled

            val fail:Boolean = (dpllResult != cdclResult || dpllResult != watchedLiteralResult)
            assertFalse(fail)

            if (cdclResult)
            {
                //if formula is satisfied, then it must also be an implicant
                //test that while we're here
                val isImplicant = isImplicant(curClauseSetCdcl)
                assertTrue(isImplicant)


                //val cdclCopyTable:CdclTable = cdclSolve(watchedLiteralClauseSet)
                val piNonWl = getPrimeImplicant(curClauseSetCdcl)
                val piWithWl = getPrimeImplicantWithWatchedLiterals(watchedLiteralClauseSet,watchedLiteralTable)


                val clWithPI = arrayOf(curClauseSetCdcl,watchedLiteralClauseSet)
                //clear all variable settings
                clWithPI.forEach { it.getPresentVariables().forEach { it.unset() }}
                //apply variable setting to primeImplicant
                arrayOf(piNonWl, piWithWl).forEach { it.forEach{lit:Literal -> lit.first.setTo(lit.second)} }
                //verify, that result is indeed primeImplicant
                assertFalse("ERROR: Prematurely returned PrimeImplicant",
                        clWithPI.any { getNonPrimeImplicantVariable(it).let{it is Either.Left && it.value != null}})
            }

            if (verbose) {
                println()
                println()
            }

        }
    }



    fun makeBoolCode(numVars: Int, numClauses: Int, varStep: Int):String {
        return makeBoolCode(Random(System.currentTimeMillis()), makeVarIds(numVars), numClauses, varStep)
    }
    fun makeBoolCode(randy: Random, knownVars:List<VariableIdentifier>,numClauses:Int,varStep:Int): String {
        var clauseList:MutableList<String> = mutableListOf()
        for (clauseIter: Int in 1..numClauses) {
            var varList:MutableList<String> = mutableListOf()
            var varsIter:Int = 0
            while(true) {
                varsIter += Math.abs(randy.nextInt() % varStep)+1
                if (varsIter >= knownVars.size) {
                    break
                } else {
                    var s:String =
                            if (randy.nextBoolean()) "!" else ""

                    s += knownVars[varsIter]
                    varList.add(s)
                }
            }
            if(!varList.isEmpty())
                clauseList.add(varList.joinToString(separator="|"))
        }
        return clauseList.joinToString(separator = " & ")
    }


    fun isLiteralSetDifferent(setA:List<Literal>,setB:List<Literal>):Boolean
    {
        if (setA.size != setB.size) {
            return true
        }
        val itA = setA.iterator()
        val itB = setB.iterator()

        while (itA.hasNext()) {
            assert(itB.hasNext())
            var a:Literal = itA.next()
            var b:Literal = itB.next()
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
        println(getPrimeImplicant(fehlerKlaus1))
        println(getPrimeImplicantWithWatchedLiterals(fehlerKlaus2))

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

        println(getPrimeImplicant(fehlerKlaus1))
        println(getPrimeImplicantWithWatchedLiterals(fehlerKlaus2))

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
        println(getPrimeImplicant(fehlerKlaus1))
        println()

        val table = cdclSolve(fehlerKlaus2)
        fehlerKlaus2.printVarSettings()
        println(getPrimeImplicantWithWatchedLiterals(fehlerKlaus2,table))
        println()

        val table3 = cdclSolve(fehlerKlaus3)
        fehlerKlaus3.printVarSettings()
        println(getPrimeImplicant(fehlerKlaus3))
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
        println(getPrimeImplicant(fehlerKlaus1))
        println()

        val table = cdclSolve(fehlerKlaus2)
        fehlerKlaus2.printVarSettings()
        println(getPrimeImplicantWithWatchedLiterals(fehlerKlaus2,table))
        println()

        val table3 = cdclSolve(fehlerKlaus3)
        fehlerKlaus3.printVarSettings()
        println(getPrimeImplicant(fehlerKlaus3))
    }

    @Test
    fun testBackbone():Unit
    {
        val fa = ClauseSetWatchedLiterals("a & a|b|c")
        val bba = getBackboneKaiKue(fa)//has backbone of A
        var success:Boolean = bba.size == 1 && bba.contains(Literal(fa.findVariable("a")!!,true))
        assert(success)

        val fb = ClauseSetWatchedLiterals("!a & a|b")
        val bbb = getBackboneKaiKue(fb)// has backbone of !a,b
        success = bbb.size == 2 && bbb.contains(Literal(fb.findVariable("a")!!,false)) &&
                bbb.contains(Literal(fb.findVariable("b")!!,true))
        assert(success)

        val fc = ClauseSetWatchedLiterals("D|!G|!J & D|!I|J & F|!J|!K & F|I & !F|!J & B|!F|!I & F|!J & D|!G & !F|G & !F|!G & !F|!J & !D|!F|!G|!K & !F|!G|K & M|N")
        val bbc = getBackboneKaiKue(fc)//has a backbone of [(D, true), (F, false), (I, true), (J, false)]
        success = bbc.size == 4 && bbc.contains(Literal(fc.findVariable("D")!!,true)) &&
                bbc.contains(Literal(fc.findVariable("F")!!,false)) &&
                bbc.contains(Literal(fc.findVariable("I")!!,true)) &&
                bbc.contains(Literal(fc.findVariable("J")!!,false))
        assert(success)




    }

    fun testBackboneStocha() {
        val randy:Random = Random(1253132)
        val knownVars = makeVarIds(8)

        for (i in IntStream.range(0, 100)) {
            var boolCode:String = makeBoolCode(randy,knownVars,10, 4)
            val klaus = ClauseSetWatchedLiterals(boolCode)

            println("Finding backbone for formula: ")
            println(klaus)
            val bb = getBackboneKaiKue(klaus,false)
            val bbc = getBackboneKaiKue(klaus,true)
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
        val varA:Variable = k.getPresentVariables().find { it.id == "a" }!!
        val varB:Variable =k.getPresentVariables().find { it.id == "b" }!!
        val varC:Variable =k.getPresentVariables().find { it.id == "c" }!!

        varA.setTo(VariableSetting.True)
        assertFalse( k.isFulfilled)
        assertFalse( k.isEmpty)
        assertFalse( isImplicant(k))
        assertFalse( isPrimeImplicant(k))

        varB.setTo(true)
        assertTrue(k.isFulfilled)
        assertTrue(isImplicant(k))
        assertTrue( isPrimeImplicant(k))

        varC.setTo(true)
        assertTrue(isImplicant(k))
        assertTrue(!isPrimeImplicant(k))

        varC.setTo(false)
        assertTrue(isImplicant(k))
        assertTrue(! isPrimeImplicant(k))

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
    fun testQuickBackbone()
    {
        val numTests:Int = 40
        val numVars:Int = 30
        val numClauses:Int = 100
        val varStep:Int = 16

        val randy = Random()

        var knownVars = makeVarIds(numVars)
        var numFails:Int = 0
        var runTests:Int = 0

        var sumMsecKaiKueSlow:Int = 0
        var sumMsecKaiKueFast:Int = 0
        var sumMsecIntersect:Int = 0

        var numKaiKueRuns:Int = 0
        var numIntersectRuns:Int = 0

        for (_iter:Int in 1..numTests) {
            val code:String = makeBoolCode(randy,knownVars,numClauses,varStep)

            if (cdclSAT(ClauseSetWatchedLiterals(code)))
            {
                runTests++

                val t1 = System.currentTimeMillis()
                val kaiKueSlow: Set<Literal> = getBackboneKaiKue(ClauseSetWatchedLiterals(code), false)
                val kaiKueSlowRuns = numCdclRuns
                val t2 = System.currentTimeMillis()

                val t3 = System.currentTimeMillis()
                val kaiKue: Set<Literal> = getBackboneKaiKue(ClauseSetWatchedLiterals(code))
                val kaiKueRuns = numCdclRuns
                val t4 = System.currentTimeMillis()
                val t5 = System.currentTimeMillis()
                val inters: Set<Literal> = getBackboneIntersections(ClauseSetWatchedLiterals(code))
                val intersRuns = numCdclRuns
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
}


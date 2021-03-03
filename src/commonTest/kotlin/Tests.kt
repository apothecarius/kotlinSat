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
import kotlin.math.abs
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
            var varsIter = 0
            while(true) {
                varsIter += abs(Random.nextInt() % varStep)+1
                if (varsIter >= knownVars.size) {
                    break
                } else {
                    var s:String =
                            if (Random.nextBoolean()) "!" else ""

                    s += knownVars[varsIter]
                    varList.add(s)
                }
            }
            if(varList.isNotEmpty())
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
            assertTrue(itB.hasNext() )
            val a: Literal = itA.next()
            val b: Literal = itB.next()
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

    @Test
    fun primeImplicantError()
    {
        //Computing the prime implicant on this formula yields a literal too much
        val algos:List<(ClauseSetWatchedLiterals) -> Set<Pair<Variable,Boolean>>> = listOf(
            { x:ClauseSetWatchedLiterals -> Implicant.getPrimeImplicant(x) },
            { x:ClauseSetWatchedLiterals -> Implicant.getPrimeImplicantWithWatchedLiterals(x) }
        )
        val names = arrayOf("BruteForce","WatchedLiteral")
        val errorIndicator:(Int)->String = { idx:Int -> "Error in prime implicant" +
                " computation with algorithm ${names[idx]}" }
        for ((algoIdx,primeImplicantAlgorithm) in algos.withIndex())
        {
            val fehlerKlausCode = "!C|!E & !B|D & !B|D|!E & B|C|D & !B|!D & !C|!E & C|!D & C"
            val fehlerKlaus = ClauseSetWatchedLiterals(fehlerKlausCode)

            //Typically "+C,-E,-B,+D" is found as prime implicant (on good luck), but +D is not required in that
            //"+C,-E,-B is actually the backbone and satisfies the formula, so it MUST be yielded
            val primeImplicant = primeImplicantAlgorithm(fehlerKlaus)

            assertEquals(3, primeImplicant.size,errorIndicator(algoIdx))
            val varB = primeImplicant.find { it.first.id == "B" }!!
            val varC = primeImplicant.find { it.first.id == "C" }!!
            val varE = primeImplicant.find { it.first.id == "E" }!!
            assertEquals(false, varB.predicate,errorIndicator(algoIdx))
            assertEquals(true, varC.predicate,errorIndicator(algoIdx))
            assertEquals(false, varE.predicate,errorIndicator(algoIdx))
        }
    }

    @Test
    fun implicantTest2()
    {
        val fehlerKlausCode = "E & B|E & B|!D & B|D|E & !D|E"
        //error to search: the watched literal solver used to find a prime implicant
        // with "-B", but that cant be, because -B is not in the formula
        val fehlerKlaus1 = ClauseSetWatchedLiterals(fehlerKlausCode)
        val fehlerKlaus2 = ClauseSetWatchedLiterals(fehlerKlausCode)
        cdclSAT(fehlerKlaus1)
        cdclSAT(fehlerKlaus2)

        val pi1 = Implicant.getPrimeImplicant(fehlerKlaus1)
        val pi2 = Implicant.getPrimeImplicantWithWatchedLiterals(fehlerKlaus1)
        assertTrue(pi1.find { it.variable.id == "B" && !it.predicate } == null)
        assertTrue(pi2.find { it.variable.id == "B" && !it.predicate } == null)

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
        val fehlerKlausCode = "C|!G & D|!F|I & !C|I & !F|G|K & G & D|!I & " +
                "!E|!J|K & !D|!E|I|J & C|!G|H|I|K & B|D|!F|!I|!J & !B|H|I & C|!I|!J"
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
    fun testBackbone()
    {
        val fa = ClauseSetWatchedLiterals("a & a|b|c")
        val bba = Backbone.getBackboneKaiKue(fa)//has backbone of A
        var success:Boolean = bba.size == 1 &&
                bba.contains(Literal(fa.findVariable("a")!!, true))
        assertTrue(success)

        val fb = ClauseSetWatchedLiterals("!a & a|b")
        val bbb = Backbone.getBackboneKaiKue(fb)// has backbone of !a,b
        success = bbb.size == 2 && bbb.contains(Literal(fb.findVariable("a")!!, false)) &&
                bbb.contains(Literal(fb.findVariable("b")!!, true))
        assertTrue(success)

        val fc = ClauseSetWatchedLiterals("D|!G|!J & D|!I|J & F|!J|!K & " +
                "F|I & !F|!J & B|!F|!I & F|!J & D|!G & !F|G & !F|!G & " +
                "!F|!J & !D|!F|!G|!K & !F|!G|K & M|N")
        val bbc = Backbone.getBackboneKaiKue(fc)//has a backbone of
        // [(D, true), (F, false), (I, true), (J, false)]
        success = bbc.size == 4 && bbc.contains(Literal(fc.findVariable("D")!!, true)) &&
                bbc.contains(Literal(fc.findVariable("F")!!, false)) &&
                bbc.contains(Literal(fc.findVariable("I")!!, true)) &&
                bbc.contains(Literal(fc.findVariable("J")!!, false))
        assertTrue(success)




    }

    fun testBackboneStocha() {
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
                println("With optimization: $bbc")
                println("Without optimization:$bb")
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
    fun activityInitializationTest()
    {
        val form = ClauseSetWatchedLiterals("a|b|c & b|!a & !c|a | d")
        for (vari: Variable in form.getPresentVariables()) {
            assertEquals(when(vari.id){
                "a" -> 3f
                "b" -> 2f
                "c" -> 2f
                "d" -> 1f
                else -> {
                    fail()
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

}


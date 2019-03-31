import com.sun.org.apache.xpath.internal.operations.Bool
import java.util.*
import java.util.stream.IntStream

/**
 * create random clausesets and compare the result of DPLL and CDCL solvers
 *
 */
fun testSolvers(numTests:Int,numVars:Int,numClauses:Int,varStep:Int): Boolean {
    assert(numVars < 26)

    val randy: Random = Random()

    val knownVars:List<Char> = makeVarIds(numVars)

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

        if (dpllResult != cdclResult || dpllResult != watchedLiteralResult) {
            println("ERROR: "+ boolCode)
            return false
        } else if (cdclResult) {
            //if formula is satisfied, then it must also be an implicant
            //test that while we're here
            val isImplicant = isImplicant(curClauseSetCdcl)
            if (!isImplicant) {
                println("ERROR: satisfied term is not implicant")
                println(boolCode)
                return false
            }


            //val cdclCopyTable:CdclTable = cdclSolve(watchedLiteralClauseSet)
            val piNonWl = getPrimeImplicant(curClauseSetCdcl)
            val piWithWl = getPrimeImplicantWithWatchedLiterals(watchedLiteralClauseSet,watchedLiteralTable)


            val clWithPI = arrayOf(curClauseSetCdcl,watchedLiteralClauseSet)
            //clear all variable settings
            clWithPI.forEach { it.getPresentVariables().forEach { it.unset() }}
            //apply variable setting to primeImplicant
            arrayOf(piNonWl, piWithWl).forEach { it.forEach{lit:Literal -> lit.first.setTo(lit.second)} }
            //verify, that result is indeed primeImplicant
            if (clWithPI.any { getNonPrimeImplicantVariable(it) != null }) {
                println("ERROR: Prematurely returned PrimeImplicant")
                println(boolCode)
                return false
            }



           // println(getPrimeImplicantWithWatchedLiterals(fehlerKlaus2))


            /*var unnecessaryVariable:Variable? = getNonPrimeImplicantVariable(curClauseSetDpll)
            while (unnecessaryVariable != null) {
                unnecessaryVariable.setTo(VariableSetting.Unset)
                unnecessaryVariable = getNonPrimeImplicantVariable(curClauseSetDpll)
            }
            if ((!curClauseSetDpll.isFulfilled) || (!isPrimeImplicant(curClauseSetDpll))
                    || (!isImplicant(curClauseSetDpll))) {
                println("ERROR: could not properly find primeImplicant")
                println(boolCode)
                return false
            }*/
        }

        if (verbose) {
            println()
            println()
        }

    }
    println("CDCL and DPLL Solvers work equally")
    return true
}

fun makeVarIds(numVars: Int): List<Char> {
    var retu = mutableListOf<Char>()
    for (i: Int in 64..64 + numVars) {
        retu.add(i.toChar())
    }
    return retu
}

fun makeBoolCode(numVars: Int, numClauses: Int, varStep: Int):String {
    return makeBoolCode(Random(System.currentTimeMillis()), makeVarIds(numVars), numClauses, varStep)
}
fun makeBoolCode(randy: Random, knownVars:List<Char>,numClauses:Int,varStep:Int): String {
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

                s += knownVars.get(varsIter)
                varList.add(s)
            }
        }
        if(!varList.isEmpty())
            clauseList.add(varList.joinToString(separator="|"))
    }
    return clauseList.joinToString(separator = " & ")
}


fun testImplicant() {
    var numTests=500
    var numVars=40
    var numClauses=325
    var varStep=16

    val randy: Random = Random()

    var knownVars = mutableListOf<Char>()
    for (i: Int in 65..65 + numVars) {
        knownVars.add(i.toChar())
    }
    var numFails:Int = 0
    var runTests:Int = 0
    for (_iter:Int in 1..numTests) {
        var boolCode: String = makeBoolCode(randy, knownVars, numClauses, varStep)
        if (verbose) {
            println(boolCode)
        }
        var cs = ClauseSetWatchedLiterals(boolCode)

        cdclSolve(cs)
        if(!cs.isFulfilled){
            //cant find implicant of unsolvable formula
            continue
        }

        runTests++

        val basePI : List<Literal> = getPrimeImplicant(cs).sortedBy { it.first.id }


        var csCopy = ClauseSetWatchedLiterals(boolCode)
        val table = cdclSolve(csCopy)
        val watchedLitPI = getPrimeImplicantWithWatchedLiterals(csCopy,table).sortedBy { it.first.id }

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

        if (isLiteralSetDifferent(basePI,watchedLitPI)) {
            println(boolCode + " => "+cs.toString())
            println("Base: "+basePI)
            println("WL: "+watchedLitPI)
            println()
            numFails++
        }
        else if (verbose) {
            println(boolCode + " => "+cs.toString())
            println(basePI)
        }

        //TODO ausgabe sortieren und dann automatisch verlgeichen
    }
    println("Fails: "+numFails+"/"+runTests)
}


fun ClauseSet.countSetVars():Int = this.getPresentVariables().count{ !it.isUnset }

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

fun testBackbone():Boolean
{
    var success:Boolean = true
    val fa = ClauseSetWatchedLiterals("a & a|b|c")
    val bba = getBackboneKaiKue(fa)//has backbone of A
    success = success && bba.size == 1 && bba.contains(Literal(fa.findVariable("a")!!,true))

    val fb = ClauseSetWatchedLiterals("!a & a|b")
    val bbb = getBackboneKaiKue(fb)// has backbone of !a,b
    success = success && bbb.size == 2 && bbb.contains(Literal(fb.findVariable("a")!!,false)) &&
            bbb.contains(Literal(fb.findVariable("b")!!,true))

    val fc = ClauseSetWatchedLiterals("D|!G|!J & D|!I|J & F|!J|!K & F|I & !F|!J & B|!F|!I & F|!J & D|!G & !F|G & !F|!G & !F|!J & !D|!F|!G|!K & !F|!G|K & M|N")
    val bbc = getBackboneKaiKue(fc)//has a backbone of [(D, true), (F, false), (I, true), (J, false)]
    println(bbc)
    success = success && bbc.size == 4 && bbc.contains(Literal(fc.findVariable("D")!!,true)) &&
            bbc.contains(Literal(fc.findVariable("F")!!,false)) &&
            bbc.contains(Literal(fc.findVariable("I")!!,true)) &&
            bbc.contains(Literal(fc.findVariable("J")!!,false))


    println(if (success) {
        "Test of backbone succeeded"
    } else {
        "Test of backbone failed"
    })
    return success
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

fun testImplicantOld() {
run{
    val k = ClauseSet("a & b|c")
    val varA:Variable = k.getPresentVariables().find { it.id == "a" }!!
    val varB:Variable =k.getPresentVariables().find { it.id == "b" }!!
    val varC:Variable =k.getPresentVariables().find { it.id == "c" }!!

    varA.setTo(VariableSetting.True)
    assert(! k.isFulfilled)
    assert(! k.isEmpty)
    assert(! isImplicant(k))
    assert(! isPrimeImplicant(k))

    varB.setTo(true)
    assert(k.isFulfilled)
    assert(isImplicant(k))
    assert( isPrimeImplicant(k))

    varC.setTo(true)
    assert(isImplicant(k))
    assert(!isPrimeImplicant(k))

    varC.setTo(false)
    assert(isImplicant(k))
    assert(! isPrimeImplicant(k))
}

return
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



    /*println(erg1.filter { it.reason is Reason.InUnitClause }.size)
    println(erg2.filter { it.reason is Reason.InUnitClause }.size)
    erg1.print()*/
}


fun testQuickBackbone() {
    var numTests=10
    var numVars=4
    var numClauses=6
    var varStep=3

    val randy: Random = Random()

    var knownVars = makeVarIds(numVars)
    var numFails:Int = 0
    var runTests:Int = 0

    for (_iter:Int in 1..numTests) {
        val code:String = makeBoolCode(randy,knownVars,numClauses,varStep)

        if (cdclSAT(ClauseSetWatchedLiterals(code)))
        {

            val tx1 = System.currentTimeMillis()
            val estim: Set<Literal> = getCdclDefaultIntersection(ClauseSetWatchedLiterals(code))
            val tx2 = System.currentTimeMillis()

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

            val failure:Boolean = kaiKue.size != inters.size
            if (failure) {
                println(code)
                println(inters)
            }

            println("mSecs:" + (t2 - t1) + "   " + (t4 - t3) + "   " + (t6 - t5))
            println("Runs: " + kaiKueSlowRuns + "   " + kaiKueRuns + "   " + intersRuns)
            println("numBB:" + estim.size + "   " + kaiKueSlow.size + "   " + kaiKue.size + "   " + inters.size + "   ")

            println()
        }
        else {
            print(",")
        }
       // println("skipping")

    }
    println("done")
}
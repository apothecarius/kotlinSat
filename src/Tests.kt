import java.util.*

/**
 * create random clausesets and compare the result of DPLL and CDCL solvers
 *
 */
fun testSolvers(numTests:Int,numVars:Int,numClauses:Int,varStep:Int): Boolean {
    assert(numVars < 26)

    val randy: Random = Random()

    var knownVars = mutableListOf<Char>()
    for (i: Int in 65..65 + numVars) {
        knownVars.add(i.toChar())
    }

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
                var s:String
                if (randy.nextBoolean()) {
                    s = "!"
                } else
                    s = ""
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
    var numTests=10
    var numVars=4
    var numClauses=7
    var varStep=2

    val randy: Random = Random()

    var knownVars = mutableListOf<Char>()
    for (i: Int in 65..65 + numVars) {
        knownVars.add(i.toChar())
    }

    for (_iter:Int in 1..numTests) {
        var boolCode: String = makeBoolCode(randy, knownVars, numClauses, varStep)
        var cs = ClauseSetWatchedLiterals(boolCode)

        cdclSolve(cs)
        if(!cs.isFulfilled){
            //cant find implicant of unsolvable formula
            continue
        }
        println(cs.toString())
        println("Base:"+getPrimeImplicant(cs))

        var csCopy = ClauseSetWatchedLiterals(boolCode)
        val table = cdclSolve(csCopy)

        println("WL:  "+getPrimeImplicantWithWatchedLiterals(csCopy,table))
        println()
        //TODO ausgabe sortieren und dann automatisch verlgeichen
    }
}


fun ClauseSet.countSetVars():Int = this.getPresentVariables().count{ !it.isUnset }

fun implicantTest1()
{
    //fehlerfall 1: mit WL hat ein unnötiges literal
    val fehlerKlausCode = "!C|!E & !B|D & !B|D|!E & B|C|D & !B|!D & !C|!E & C|!D & C"
    val fehlerKlaus1 = ClauseSetWatchedLiterals(fehlerKlausCode);
    val fehlerKlaus2 = ClauseSetWatchedLiterals(fehlerKlausCode);
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

    val fc = ClauseSetWatchedLiterals("D|!G|!J & D|!I|J & F|!J|!K & F|I & !F|!J & B|!F|!I & F|!J & D|!G & !F|G & !F|!G & !F|!J & !D|!F|!G|!K & !F|!G|K")
    val bbc = getBackboneKaiKue(fc)//has a backbone of [(D, true), (F, false), (I, true), (J, false)]
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
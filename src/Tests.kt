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
        var boolCode:String = clauseList.joinToString(separator = " & ")
        if (verbose) {
            println(boolCode)
        }

        val curClauseSetDpll = ClauseSet(boolCode)
        val curClauseSetCdcl = ClauseSet(boolCode)//ClauseSetWatchedLiterals(boolCode)
        val watchedLiteralClauseSet = ClauseSetWatchedLiterals(boolCode)
        val dpllResult:Boolean = dpllSAT(curClauseSetDpll)
        val cdclResult:Boolean = cdclSAT(curClauseSetCdcl)
        val watchedLiteralResult:Boolean = cdclSAT(watchedLiteralClauseSet)

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
            //unset variables until formula is primeImplicant
            var unnecessaryVariable:Variable? = getNonPrimeImplicantVariable(curClauseSetDpll)
            while (unnecessaryVariable != null) {
                unnecessaryVariable.setTo(VariableSetting.Unset)
                unnecessaryVariable = getNonPrimeImplicantVariable(curClauseSetDpll)
            }
            if ((!curClauseSetDpll.isFulfilled) || (!isPrimeImplicant(curClauseSetDpll))
                    || (!isImplicant(curClauseSetDpll))) {
                println("ERROR: could not properly find primeImplicant")
                println(boolCode)
                return false
            }
        }

        if (verbose) {
            println()
            println()
        }

    }
    println("CDCL and DPLL Solvers work equally")
    return true
}


fun testImplicant() {
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
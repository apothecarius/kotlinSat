import java.util.*

val verbose:Boolean = true

fun main(args : Array<String>)
{
    //clauseTest()
    //interesting testcase with 3 conflicts
    //val klaus = ClauseSet(" !aX|bX & bX|aX & !bX|aX & !bX|!aX & D|!G|!J|!L&D|!I|J&C|E|F|!J|!K|M&F|I&!E|!F|!J&B|E|!F|!I&!C|H|!I|J|!K&E|F|!K|L&D|G|!J&C|F|J&F|!I&C|G|J|K|!L&!E|!H|!I|!K&F|!J&D|!G|L&!F|G|L&!F|!G|L&!F|!J&!D|!F|!G|!K&!F|!G|K")
    testSolvers(50, 4, 7, 2)
    val unklaus = ClauseSetWatchedLiterals("!C|!D|!E & !C|!E & B|!D|!E & C|E & !C|D & C|D & B|C|!E") //&C works
    cdclSAT(unklaus)
    //cdclSAT(unklaus)
    //cdclSAT(klaus)
}

/**
 * create random clausesets and compare the result of DPLL and CDCL solvers
 *
 */
fun testSolvers(numTests:Int,numVars:Int,numClauses:Int,varStep:Int): Boolean {
    assert(numVars < 26)

    val randy:Random = Random()

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
        }
        println()
        println()

    }
    println("CDCL and DPLL Solvers work equally")
    return true
}
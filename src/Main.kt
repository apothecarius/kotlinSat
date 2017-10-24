import java.util.*

fun main(args : Array<String>)
{
    //interesting testcase with 3 conflicts
    // D|!G|!J|!L&D|!I|J&C|E|F|!J|!K|M&F|I&!E|!F|!J&B|E|!F|!I&!C|H|!I|J|!K&E|F|!K|L&D|G|!J&C|F|J&F|!I&C|G|J|K|!L&!E|!H|!I|!K&F|!J&D|!G|L&!F|G|L&!F|!G|L&!F|!J&!D|!F|!G|!K&!F|!G|K

    testSolvers(5,12,20,5)
    return

    var a = Variable(c="a")
    var b = Variable(c="b")
    var c = Variable(c="c")

    var klausContent:Array<Pair<Variable,Boolean>> = arrayOf(Pair(a,true),Pair(c,true))
    val klaus:Clause = Clause(klausContent)

    klausContent = arrayOf(Pair(a,false),Pair(b,false))
    val klara:Clause = Clause(klausContent)
    var res1:Resolvent = makeResolvent(klara)
    var res2:Resolvent = makeResolvent(klaus)

    klausContent = arrayOf(Pair(a,false),Pair(b,true))
    val kolette:Clause = Clause(klausContent)

    val klosett = ClauseSet(arrayOf(klaus,klara,kolette))



    val wasserklo = ClauseSet("!a|b & !a|!b")

    cdclSAT(wasserklo)
    println()
    wasserklo.printVarSettings()
    wasserklo.printClauses()
}

/**
 * create random clausesets and compare the result of DPLL and CDCL solvers
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
        var boolCode:String = clauseList.joinToString(separator = "&")
        println(boolCode)


        val curClauseSetDpll = ClauseSet(boolCode)
        val curClauseSetCdcl = ClauseSet(boolCode)
        val dpllResult:Boolean = curClauseSetDpll.dpllSAT()
        val cdclResult:Boolean = cdclSAT(curClauseSetCdcl)

        if (dpllResult != cdclResult) {
            println("ERROR: "+ boolCode)
            return false
        }

    }
    return true
}
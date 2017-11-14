import kotlin.coroutines.experimental.buildSequence

val verbose:Boolean = false

fun main(args : Array<String>)
{
    //testImplicant()
    //interesting testcase with 3 conflicts
    //val klaus = ClauseSet(" !aX|bX & bX|aX & !bX|aX & !bX|!aX & D|!G|!J|!L&D|!I|J&C|E|F|!J|!K|M&F|I&!E|!F|!J&B|E|!F|!I&!C|H|!I|J|!K&E|F|!K|L&D|G|!J&C|F|J&F|!I&C|G|J|K|!L&!E|!H|!I|!K&F|!J&D|!G|L&!F|G|L&!F|!G|L&!F|!J&!D|!F|!G|!K&!F|!G|K")
    //dont call the other tests if an error is found in the first run
    if(testSolvers(numTests=500, numVars=4, numClauses=7, varStep=2))
        testSolvers(500,10,10,7)

    //val unklaus = ClauseSetWatchedLiterals("!B|D & B|D & !C|E & !B|D & C|E & C|!E & !C|!E") //&C works
    //cdclSAT(unklaus)
    //cdclSAT(unklaus)
    //cdclSAT(klaus)
}



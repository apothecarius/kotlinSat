import javax.print.attribute.IntegerSyntax

const val verbose:Boolean = false

enum class WatchedLiteralIterationScheme {
    ToMiddle, SideBySide
}
val activeWLIterationScheme:WatchedLiteralIterationScheme = WatchedLiteralIterationScheme.ToMiddle



fun main(args : Array<String>)
{
    //implicantTest4()
    //val bb1 = ClauseSetWatchedLiterals("a & a|b|c")
    //val bb2 = ClauseSetWatchedLiterals("!a & a|b")

    /*var x:Variable = Variable("a")
    var y: Variable = Variable("a")
    println(x.equals(y))
    var l: Literal = Literal(x, true)
    var k:Literal = Literal(y,true)
    println(l.equals(k))
    val m = mapOf<Variable, Int>(x to 15).containsKey(y)
    println(m)*/
    //klausWL.printClauses()
    //val table = cdclSolve(klausWL)
    //table.print()

    //println(getPrimeImplicantWithWatchedLiterals(klausWL,table))
    //println(getPrimeImplicant(klaus))
//    println(klaus.getLiteralOccurences())

    /*var table = cdclSolve(klaus)
    println(klaus.isFulfilled)
    table.print()
    for (v in table.getUnitVariables()) {
        println(v.setting)
    }*/

    //testImplicant()
    //interesting testcase with 3 conflicts
    //val unklaus = ClauseSet(" !aX|bX & bX|aX & !bX|aX & !bX|!aX & D|!G|!J|!L&D|!I|J&C|E|F|!J|!K|M&F|I&!E|!F|!J&B|E|!F|!I&!C|H|!I|J|!K&E|F|!K|L&D|G|!J&C|F|J&F|!I&C|G|J|K|!L&!E|!H|!I|!K&F|!J&D|!G|L&!F|G|L&!F|!G|L&!F|!J&!D|!F|!G|!K&!F|!G|K")
    //val klaus = ClauseSetWatchedLiterals("D|!G|!J & D|!I|J & F|!J|!K & F|I & !F|!J & B|!F|!I & F|!J & D|!G & !F|G & !F|!G & !F|!J & !D|!F|!G|!K & !F|!G|K")
    //cdclSolve(klaus).print()
    //println(klaus.isFulfilled)
    //cdclSAT(unklaus)
    //cdclSAT(klaus)
/*
    //dont call the other tests if an error is found in the first run
    if(testSolvers(numTests=1000, numVars=4, numClauses=7, varStep=2))
        if (testSolvers(1000, 10, 12, 6))
            testImplicant()
    */
    testBackbone()
}



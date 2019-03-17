

const val verbose:Boolean = false

enum class WatchedLiteralIterationScheme {
    ToMiddle, SideBySide
}
val activeWLIterationScheme:WatchedLiteralIterationScheme = WatchedLiteralIterationScheme.ToMiddle



fun main(args:Array<String>)
{
    //clauseset where primeImplicatWithWatchedLiterals fails
    val unpi1 = ClauseSetWatchedLiterals("B|C|!E & !C|E & !D & B|!C")
    val unpi2 = ClauseSetWatchedLiterals("!B|!D & !D|E & !D|!E & !C|!E")
    val unpi3 = ClauseSetWatchedLiterals("B|!E & B|C|E & B|!E & !B|!C|D")
    val table = cdclSolve(unpi3)

    println("\n"+getPrimeImplicant(unpi3))
    val unpi3_ = ClauseSetWatchedLiterals("B|!E & B|C|E & B|!E & !B|!C|D")
    val table_ = cdclSolve(unpi3_)
    println("\n"+getPrimeImplicantWithWatchedLiterals(unpi3_))
    //interessante formeln für CDCL Zeilenverschieben
    //println(getBackboneKaiKue(klaus)) NIX GRAD
    //println()
    //println(getBackboneKaiKue(klaus2))

    //!B|!C|D|F & D|!F & B|!D & D|F & C|E & B|E & B|!C|F
    //D wird gelernt, wird aber nicht auf level 0 evaluiert
    //implicantTest4()
    //val bb1 = ClauseSetWatchedLiterals("C|D|F & B|C|D|!E|!F & !B|!C|D|E & C|!E & B|!D|E|!F & !C|E|F & C|E & C|D|E")
    //val klaus = ClauseSetWatchedLiterals("D|!G|!J & D|!I|J & F|!J|!K & F|I & !F|!J & B|!F|!I & F|!J & D|!G & !F|G & !F|!G & !F|!J & !D|!F|!G|!K & !F|!G|K")
    testImplicant()

    //println("\n"+getBackboneIntersections(klaus))
/*
    // TODO set of learned clauses explodes, so implement clause subsumption
    val bsat180: File = File("C:\\Users\\apoth\\Downloads\\sat competition examples\\NoLimits\\mp1-bsat180-648.cnf")
    assert(bsat180.isFile)
    val klaus = readCnf(bsat180)
    val t1 = System.currentTimeMillis()
    val result = cdclSolve(klaus)
    val t2 = System.currentTimeMillis()
    println(t2 - t1)
    println(klaus.isFulfilled)
    println(result)
    //println(getBackboneIntersections(bb1))
*/


    //val bb2 = ClauseSetWatchedLiterals("!a & a|b")
//    val xxx = cdclSolve(bb1).getAxiomaticEntries()

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
    //testBackboneStocha()


    /*val klaus = ClauseSetWatchedLiterals("!D & B|!D|!F & C|!E & !C|F & C|!F & !C|F & C|E|F")
    println(cdclSolve(klaus))
    println(getPrimeImplicant(klaus))
    println(getBackboneKaiKue(klaus))*/

    //val code:String = makeBoolCode(50,20,3)
    //testQuickBackbone()

    /*val s = makeBoolCode(1000,110,800)
    repeat(5) {
        println(cdclSAT(s))
        val bb = getBackboneIntersections(ClauseSetWatchedLiterals(s))
        println(bb)

    }*/


    //timingTests()
}



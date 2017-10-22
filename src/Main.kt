fun main(args : Array<String>)
{

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
    wasserklo.printVarSettings()
    wasserklo.printClauses()


}



/*
These functions work on (partial) solvings of clauseSet (some of its variables
are expected to be set true or false)

The term clauseSet and setting of said clauseSet is used equivalently here,
because the setting of variables is stored within the formula, in the terms of
this framework
 */


class WatchedLiteralToClause {

    private val map:MutableMap<Literal,MutableSet<ClauseWatchedLiterals>> = mutableMapOf()
    fun put(lit: Literal, clause: ClauseWatchedLiterals) {
        var container = this.map[lit]
        if (container == null) {
            container = mutableSetOf()
            this.map[lit] = container
        }
        container.add(clause)
    }

    fun get(lit: Literal):Set<ClauseWatchedLiterals> {
        var retu:Set<ClauseWatchedLiterals>? = this.map[lit]
        
        return when (retu) {
            null -> emptySet()
            else -> retu
        }
    }

    fun remove(lit: Literal, clause: ClauseWatchedLiterals) {
        var container = this.map[lit]
        if (container != null) {
            container.remove(clause)
        }
    }
}

/**
 * @return True, if the unset variables  (any combination) in clauseSet can be set
 * to either false or true and the formula would still be satisfied
 *
 * TODO test
 */
fun isImplicant(clauseSet: ClauseSet):Boolean {
    //quick checks
    if (clauseSet.isFulfilled) {
        return true
    } else if (clauseSet.isEmpty) {
        return false
    }

    //cant be null at this point
    val varToCheck:Variable = clauseSet.getAnyFreeVariable()!!
    varToCheck.setTo(VariableSetting.True)
    if (clauseSet is ClauseSetWatchedLiterals) {
        clauseSet.updateWatchedLiterals(varToCheck)
    }

    var retu: Boolean = isImplicant(clauseSet)
    varToCheck.setTo(VariableSetting.False)
    if (clauseSet is ClauseSetWatchedLiterals) {
        clauseSet.updateWatchedLiterals(varToCheck)
    }

    retu = retu && isImplicant(clauseSet) //is not called if retu is already false

    //reset variable
    varToCheck.setTo(VariableSetting.Unset)
    return retu
}


/**
 * Returns a variable which hinders this partially set clauseSet to be a
 */
fun getNonPrimeImplicantVariable(clauseSet: ClauseSet): Variable? {
    //quick check
    if (clauseSet.isEmpty) {
        return null
    } else if (!clauseSet.isFulfilled) {
        return null
    }
    //if no set variable can be made unset without the clauseSet not being implicant
    // anymore, then this would not be primeImplicant
    for (v: Variable in clauseSet.getPresentVariables()) {
        if (v.isUnset) {
            continue
        } else {
            val prevSetting:Boolean = v.boolSetting!!
            v.setTo(VariableSetting.Unset)
            val isImplWithoutV = isImplicant(clauseSet)
            v.setTo(prevSetting)
            if (isImplWithoutV) { //can be implicant without v, so is not primeImplicant
                return v
            }
        }
    }
    return null
}

/**
 * @return True, if the (partial) setting of the variables is an implicant, and
 * no variable can be set to Unset without loosing the implicant condition
 */
fun isPrimeImplicant(clauseSet: ClauseSet): Boolean =
        (getNonPrimeImplicantVariable(clauseSet) == null)


/**
 * Finds the prime implicant of the clauseSet in a primitve way
 * and returns it. After returning the variable setting is as it was previously
 *
 * TODO add support for ClauseSetWatchedLiteral, the watched literal scheme
 * seems to make problems in this case when the literals are changed (since it
 * affects the recognition of unfulfilled clauses)
 */
fun getPrimeImplicant(clauseSet: ClauseSet):Set<Literal> {
    if(clauseSet.isFresh)
        cdclSAT(clauseSet)
    assert(clauseSet.isFulfilled)
    val originalSetting:Set<Literal> = clauseSet.getVariableSetting()
    if (clauseSet is ClauseSetWatchedLiterals) {
        ClauseWatchedLiterals.watchedLiteralsForUnitVariables = false
        clauseSet.resetAllWatchedLiterals()
    }


    do{
        val nonPrime:Variable = getNonPrimeImplicantVariable(clauseSet)?:break
        nonPrime.unset()
        if(clauseSet is ClauseSetWatchedLiterals){
            clauseSet.updateWatchedLiterals(nonPrime)
        }
    }while(true)

    val retu = clauseSet.getVariableSetting()
    clauseSet.setTo(originalSetting)
    if (clauseSet is ClauseSetWatchedLiterals) {
        clauseSet.resetAllWatchedLiterals()
    }

    if (clauseSet is ClauseSetWatchedLiterals) {
        ClauseWatchedLiterals.watchedLiteralsForUnitVariables = true
    }

    return retu
}

fun  getPrimeImplicantWithWatchedLiterals(clauseSet: ClauseSetWatchedLiterals) =
        getPrimeImplicantWithWatchedLiterals(clauseSet,cdclSolve(clauseSet))
fun getPrimeImplicantWithWatchedLiterals(clauseSet: ClauseSetWatchedLiterals,
                                         table:CdclTable):Set<Literal>
{
    fun HDL_constr(checkedClause:ClauseWatchedLiterals,changedLiteral:Literal,
                   lit2clause:WatchedLiteralToClause):Boolean
    {
        //need to know, which literal was moved
        val prevWatcheds = checkedClause.getBothWatchedLiterals()
        lit2clause.remove(changedLiteral,checkedClause)

        if (activeWLIterationScheme == WatchedLiteralIterationScheme.ToMiddle)
        {
            assert(checkedClause.watchedHead <= checkedClause.watchedTail)
        }
        checkedClause.updateWatchedLiterals(changedLiteral.variable)
        if (activeWLIterationScheme == WatchedLiteralIterationScheme.ToMiddle)
        {
            assert(checkedClause.watchedHead <= checkedClause.watchedTail)
        }

        //order of cases as in paper
        if (! checkedClause.isPrimeFulfilled())
        {
            //found a new literal, so update literalToClause map
            val curWatcheds = checkedClause.getBothWatchedLiterals()
            assert(curWatcheds.second != null)
            var nuWatched:Literal =
                if (prevWatcheds.first == curWatcheds.first)
                {
                    curWatcheds.second!!
                } else if (prevWatcheds.second == curWatcheds.second)
                {
                    curWatcheds.first
                }else
                {
                    assert(false)
                    curWatcheds.first
                }

            lit2clause.put(nuWatched,checkedClause)
            assert(checkedClause.isSatisfied)
            return false
        } else
        {
            //literal is the last remaining
            //also remove the other reference, to not touch checkedclause again unnecessarily
            lit2clause.remove(checkedClause.getPrimeLiteral()!!,checkedClause)
            //assert(checkedClause.isSatisfied)
            return true
        }
    }
    //paper passes C and M, but C is never used and the relevant part of M is in the variables in the clauses in W
    fun impliedW(l:Literal,requiredLiterals:MutableSet<Literal>,literalToClause:WatchedLiteralToClause)
    {
        if (verbose) {println("w: $l")}
        //prevent concurrentmodificationException by copying
        val occurences = literalToClause.get(l).toList()
        for (clause in occurences)
        {
            if (HDL_constr(clause, l, literalToClause))
            {
                if (requiredLiterals.contains(l))
                {
                    continue
                }
                var newPrimeLiteral:Literal = clause.getPrimeLiteral()!!
                //assert(!requiredLiterals.contains(l))
                //assert(newPrimeLiteral == l)
                requiredLiterals.add(newPrimeLiteral)
                //have to give the variable its setting back, as it is now assumed that it must have this setting
                l.first.setTo(l.predicate)
                assert(clause.isSatisfied)
            }
        }
    }
    fun impliedW0(model:Set<Literal>, initialImplicant:MutableSet<Literal>,literalToClause:WatchedLiteralToClause)
    {
        val possiblyUnnecessaryLiterals:Collection<Literal> = model.filter {! initialImplicant.contains(it) }
        for (l: Literal in possiblyUnnecessaryLiterals)
        {
            println("Updating(w0): "+l)
            val prevSetting:Boolean = l.variable.boolSetting!!
            //l.variable.unset()
            impliedW(Literal(l.variable,!l.predicate),initialImplicant,literalToClause)
            l.variable.setTo(prevSetting)
        }
    }

    //prepare the clauseset to be able to reuse the clauseset object, I cant just remove falsy variables
    //clauseSet.removeFalsyVariables() //TODO cant just remove falsy variables, if I want ot reuse the clauseSet to calculate a backbone
    if (verbose) {
        println("~>"+clauseSet.toString())
    }
    clauseSet.prepareWatchedLiteralsForImplicants()


    //given the context that Variable already stores the setting of a variable
    //using a literal for elements of the model and other things seems redundant
    //however it works better like this,

    //"M" in the paper, actually not a model but a partial model, an implicant
    var model:MutableSet<Literal> = clauseSet.getPresentVariables().
            filter { ! it.isUnset }.map { it -> Literal(it,it.boolSetting!!) }.
            toMutableSet()
    //"PI" in the paper, the set of variables that are in the prime implicant
    var primeImplicant:MutableSet<Literal> = /*mutableSetOf()*///table.getUnitVariables().toMutableSet()
            clauseSet.getClauses().filter { it.literals.count() == 1 }.map { it.literals[0]}.toMutableSet()
    clauseSet.resetAllWatchedLiterals()
    //"W" in the paper
    var literalToClause:WatchedLiteralToClause = clauseSet.getWatchedLiteralToClause()


    //impliedW0(model,primeImplicant,literalToClause)

    while(true) {
        //get a literal that hasnt yet been set to
        var literalToRemove:Literal = model.filter{!primeImplicant.contains(it)}.firstOrNull() ?: break
        //println("removing "+literalToRemove)
        model.remove(literalToRemove)
        literalToRemove.variable.unset()
        impliedW(literalToRemove,primeImplicant,literalToClause)

    }


    ClauseWatchedLiterals.watchedLiteralsForUnitVariables = true
    return primeImplicant
}


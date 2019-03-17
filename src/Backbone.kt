

var numCdclRuns:Int = 0
/**
 * Kaiser-Kuechlin Algorithm to calculate backbones
 */
fun getBackboneKaiKue(cs: ClauseSetWatchedLiterals, useOptimizations:Boolean = true):Set<Literal> {

    //count CDCL runs for testing purposes
    numCdclRuns = 0

    assert(cs.getPresentVariables().all { it.isUnset })
    cs.resetVars()
    val retu = mutableSetOf<Literal>()
    val skippedVars = mutableSetOf<Variable>()
    val baseImplicant:CdclTable = cdclSolve(cs)
    numCdclRuns++
    if (cs.isEmpty) {
        return emptySet()
    }
    val defaultSettings = cs.getVariableSetting()

    //TODO schauen ob gelernte klauseln in changedFormula übernommen wurden (sollte nicht passieren)
    if (useOptimizations) {
        //unset variables cannot possibly be part of the backbone
        skippedVars.addAll(cs.getPresentVariables().filter { it.isUnset })
        //lvl 0 entries are automatically part of the backbone
        retu.addAll(baseImplicant.filter { it.level == 0}.map { it -> Literal(it.affectedVariable,it.value) })

        //make another run with CDCL but prefer the other value for decided literals
        val intersection:Set<Variable> = getCdclDefaultIntersection(cs,baseImplicant).map { it.first }.toSet()
        numCdclRuns++
        for (v: Variable in cs.getPresentVariables()) {
            if (!intersection.contains(v)) {
                skippedVars.add(v)
            }
        }


    }
    cs.resetVars()// reset so that the setting is not taken over to the adjusted testformula




    for(toCheck:Literal in if(useOptimizations){baseImplicant.filter{it.level > 0}}else{baseImplicant}.
            map { it -> Literal(it.affectedVariable, it.value) })
    {
        if (skippedVars.contains(toCheck.variable)) {
            continue
        }
        val changedFormula:ClauseSetWatchedLiterals = makeAdjustedClauseSet(cs,toCheck)
        if (verbose) {
            println("Doing backbone test for variable "+toCheck.first.id)
        }
        changedFormula.resetVars()
        val alternativeImplicant:CdclTable = cdclSolve(changedFormula)
        numCdclRuns++
        if (changedFormula.isEmpty) {
            retu.add(toCheck)
        } else {
            //add changed variables to skippedVars, so that they dont need to be rechecked
            for (toSkip: CdclTableEntry in alternativeImplicant.
                    filter { retu.map { it.first }.contains(it.affectedVariable) || skippedVars.contains(it.affectedVariable) }.
                    filter { defaultSettings.contains(Literal(it.affectedVariable,it.value)) }) {//TODO check if finding the variable actually works
                skippedVars.add(toSkip.affectedVariable)
            }
        }

    }



    return retu
}


fun makeAdjustedClauseSet(cs: ClauseSetWatchedLiterals, toNegate: Literal):ClauseSetWatchedLiterals {
    val negatedLiteral = Literal(toNegate.variable,!toNegate.predicate)
/*
    //var clauses: MutableList<Clause> = cs.copyClauses()


    clauses.add(
    })

    if (isWatchedLiterals) {
        return ClauseSetWatchedLiterals(clauses.map { it -> it as ClauseWatchedLiterals }.toTypedArray())
    } else
        return ClauseSet(clauses.toTypedArray())*/

    val retu = ClauseSetWatchedLiterals(cs,true)

    retu.addResolvent(ClauseWatchedLiterals(negatedLiteral))
    return retu
}


/**
 * @param firstSolution this function can reuse a previous result of a CDCL run.
 * The value for decisions is expected not to have changed since this table was calculated
 * @return The intersection of two CDCL runs, once with false as the value for decided variables and once false
 *
 */
fun getCdclDefaultIntersection(cs: ClauseSet, firstSolution:CdclTable? = null):Set<Literal> {

    val falseTable: CdclTable =
            if (firstSolution != null) {
                firstSolution
            } else {
                cs.resetVars();
                cdclSolve(cs)
            }

    invertDecisionVariableSetting()
    cs.resetVars()
    val trueTable: CdclTable = cdclSolve(cs)

    val retu: MutableSet<Literal> = mutableSetOf()
    for (falseEntry: CdclTableEntry in falseTable) {
        val trueEntry:CdclTableEntry? = trueTable.find { it.affectedVariable == falseEntry.affectedVariable }
        if (trueEntry != null && trueEntry.value == falseEntry.value) {
            retu.add(Literal(falseEntry.affectedVariable,falseEntry.value))
        }
    }
    invertDecisionVariableSetting()

    return retu
}


fun getBackboneIntersections(cs: ClauseSetWatchedLiterals):Set<Literal> {
    numCdclRuns = 0
    //1. run a cdcl pass
    val firstTable:CdclTable = cdclSolve(cs)
    numCdclRuns++
    if (cs.isEmpty) {
        //no backbone if clauseSet is not satisfiable at all
        return emptySet()
    }

    //boil it down to the prime implicant //TODO get prime implicant reduction to work
    //val firstPrimeImplicant:Set<Variable> = getPrimeImplicantWithWatchedLiterals(cs,firstTable).map { it.variable }.toSet()
    val firstPrimeImplicant:Set<Variable> = getPrimeImplicant(cs).map { it.variable }.toSet()

    //mark all unset variables to not be in the backbone (make LinkedHashMap "candidates" with variables to setting, in order of
    // occurence in CdclTable
    //do not insert unset variables (arent in the prime implicant anyway)
    val candidates:LinkedHashMap<Variable,Boolean> = LinkedHashMap()

    //firstTable.filter { getPrimeImplicantWithWatchedLiterals(cs,firstTable).map { it.variable }.
    //        contains(it.affectedVariable) }.forEach {candidates.put(it.affectedVariable,!it.value)}
    firstTable.filter { it.level != 0 }.forEach{candidates.put(it.affectedVariable,!it.value)}
    //TODO appearantly works even if both lines are inactive (and candidates is initially empty) investigate why //happens, when the testcase wasnt interesting


    //need to extract BB vars from a table, if no candidates exist, then we should use the previous table
    var intersectedTable:CdclTable = firstTable
    var numKnownBackboneLiterals:Int = firstTable.countAxiomaticLiterals()

    while (candidates.isNotEmpty()) {

        //2. run the CDCL on the SAME formula (with learned clauses, but reset variable settings) and pass the candidates
        // from the previous run, but use inverse settings to be used for decisions
        cs.resetVars()
        intersectedTable = cdclSolve(cs, candidates)
        numCdclRuns++

        //remove unset variables from candidates and those with different setting than is noted
        for (cdclEntry: CdclTableEntry in intersectedTable) {
            val candidateOccurence:Boolean? = candidates[cdclEntry.affectedVariable]
            if (candidateOccurence != null && candidateOccurence == cdclEntry.value) {
                //value was a candidate, but was set to something else this time
                //so it cannot be in the backbone
                candidates.remove(cdclEntry.affectedVariable)
            }
        }
        //remove candidates that were recognized as backbone
        val curAxiomaticEntries = intersectedTable.getAxiomaticEntries()
        if (curAxiomaticEntries.count() > numKnownBackboneLiterals) { //quick precheck
            numKnownBackboneLiterals = curAxiomaticEntries.count()
            for (bb: CdclTableEntry in curAxiomaticEntries) {
                candidates.remove(bb.affectedVariable)
            }
            //TODO extract axiomatic literals directly to reduce number of cdcl runs (by one)
        }


        //if candidates is empty return everything in current CdclTable on level 0
        //else reiterate
    }

    return intersectedTable.filter { it.level == 0 }.map { Literal(it.affectedVariable,it.value) }.toSet()
}
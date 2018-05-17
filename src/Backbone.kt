
/**
 * Kaiser-Kuechlin Algorithm to calculate backbones
 */
fun getBackboneKaiKue(cs: ClauseSetWatchedLiterals, useOptimizations:Boolean = true):Set<Literal> {

    assert(cs.getPresentVariables().all { it.isUnset })
    cs.resetVars()
    val retu = mutableSetOf<Literal>()
    val skippedVars = mutableSetOf<Variable>()
    val baseImplicant:CdclTable = cdclSolve(cs)
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
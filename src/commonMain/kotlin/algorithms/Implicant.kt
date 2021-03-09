package algorithms

import materials.*
import support.Either
import support.assert

/*
These functions work on (partial) solvings of clauseSet (some of its variables
are expected to be set true or false)

The term clauseSet and setting of said clauseSet is used equivalently here,
because the setting of variables is stored within the formula, in the terms of
this framework
 */


object Implicant {
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

        //reset materials.getVariable
        varToCheck.setTo(VariableSetting.Unset)
        return retu
    }


    /**
     * Returns a materials.getVariable which hinders this partially set clauseSet to be a prime implicant
     */
    fun getNonPrimeImplicantVariable(clauseSet: ClauseSet): Either<Variable?, Unit> {
        //quick check, unsatisfiable or unsatisfied formulas return nothing
        if (clauseSet.isEmpty) {
            return Either.Right(Unit)
        } else if (!clauseSet.isFulfilled) {
            //must be satisfied
            return Either.Right(Unit)
        }
        //if no set materials.getVariable can be made unset without the clauseSet not being implicant
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
                    return Either.Left(v)
                }
            }
        }
        return Either.Left(null)
    }

    /**
     * @return True, if the (partial) setting of the variables is an implicant, and
     * no materials.getVariable can be set to Unset without loosing the implicant condition
     */
    fun isPrimeImplicant(clauseSet: ClauseSet): Boolean=
            getNonPrimeImplicantVariable(clauseSet).let{
                it is Either.Left && it.value == null
            }




    /**
     * Finds the prime implicant of the clauseSet in a primitve way
     * and returns it. After returning the materials.getVariable setting is as it was previously
     *
     * TODO add support for ClauseSetWatchedLiteral, the watched literal scheme
     * TODO verify testcoverage
     * seems to make problems in this case when the literals are changed (since it
     * affects the recognition of unfulfilled clauses)
     */
    fun getPrimeImplicant(clauseSet: ClauseSet):Set<Literal>
    {
        if(clauseSet.isFresh)
            cdclSAT(clauseSet)
        assert { clauseSet.isFulfilled }
        val originalSetting:Set<Literal> = clauseSet.getVariableSetting()
        if (clauseSet is ClauseSetWatchedLiterals) {
            ClauseWatchedLiterals.watchedLiteralsForUnitVariables = false
            clauseSet.resetAllWatchedLiterals()
        }


        do{
            val nonPrime:Variable = getNonPrimeImplicantVariable(clauseSet).let {
                if(it is Either.Left && it.value != null)
                    it.value
                else null
            } ?: break

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

    fun getPrimeImplicantWithWatchedLiterals(clauseSet: ClauseSetWatchedLiterals) =
            getPrimeImplicantWithWatchedLiterals(clauseSet,cdclSolve(clauseSet))
    fun getPrimeImplicantWithWatchedLiterals(clauseSet: ClauseSetWatchedLiterals,
                                             table:CdclTable):Set<Literal>
    {
        //set the literalwatches to propagate for this purpose
        ClauseWatchedLiterals.watchedLiteralsForUnitVariables = false
        //return table.map { Literal(it.affectedVariable,it.value) }.toSet()
        val primeImplicant = mutableListOf<Literal>()
        //add all unit propagated assignments because they are always part of
        // the prime implicant
        primeImplicant.addAll(table.filter { it.reason is  Reason.InUnitClause}.map {
            Literal(it.affectedVariable,it.value) })

        //go through the CdclTable top to bottom, skip propagations, and check whether
        // some clause needs the decision. If so take it into retu, if not unassign it

        table.filter { it.reason is Reason.Decision}.reversed().forEach {
                (_,assignedVar,literalPhase,_) ->
            val assocClauses = clauseSet.getOccurencesLookup()[assignedVar]!!
            val isRequired:Boolean = assocClauses.any { it.isUnit }

            if (isRequired) {
                primeImplicant.add(Literal(assignedVar,literalPhase))
            }else{
                assignedVar.unset()
                assocClauses.forEach { it.updateWatchedLiterals(assignedVar) }
            }
        }

        //revert literalwatches so that they serve the purpose of finding models, as expected
        ClauseWatchedLiterals.watchedLiteralsForUnitVariables = true
        return primeImplicant.toSet()
    }


}


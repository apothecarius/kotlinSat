
/*
These functions work on (partial) solvings of clauseSet (some of its variables
are expected to be set true or false)

The term clauseSet and setting of said clauseSet is used equivalently here,
because the setting of variables is stored within the formula, in the terms of
this framework
 */

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
    var retu: Boolean = isImplicant(clauseSet)
    varToCheck.setTo(VariableSetting.False)
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

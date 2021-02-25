package algorithms
import materials.ClauseSet
import materials.Variable
import materials.VariableSetting

fun dpllSAT(clauseSet: ClauseSet):Boolean
{
    val unitVars:List<Variable> = clauseSet.setUnits()
    if (clauseSet.isEmpty) {
        clauseSet.resetVars(unitVars)
        return false
    } else if (clauseSet.isFulfilled) {
        return true
    }

    //there must be any free materials.getVariable, that is needs to
    //be set in a nontrivial way
    val freeVariable: Variable = clauseSet.getAnyFreeVariable()!!
    //if this would fail, then all variables have to be set already
    //but then one of the above checks on whether the clauseset is already empty
    //or fulfilled would have returned true, and this line wouldn't have been
    //reached

    //try setting to true and do recursion
    freeVariable.setTo(VariableSetting.True)
    val workedWithTrue:Boolean = dpllSAT(clauseSet)
    if(workedWithTrue)
        return true
    //try false
    freeVariable.setTo(VariableSetting.False)
    val workedWithFalse:Boolean = dpllSAT(clauseSet)
    if (workedWithFalse) {
        return true
    }
    //the given setting of variables is not working
    clauseSet.resetVars(unitVars+freeVariable)
    return false
}
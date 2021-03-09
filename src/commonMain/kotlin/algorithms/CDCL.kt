package algorithms

import materials.*
import support.assert

data class CdclTableEntry(
        val level:Int,
        val affectedVariable: Variable,
        val value:Boolean,
        val reason:Reason)

typealias CdclTable = MutableList<CdclTableEntry>
fun CdclTable.findReason(forVar: Variable):Reason? =
        this.find { it.affectedVariable == forVar }?.reason

fun CdclTable.getAxiomaticEntries(): Sequence<CdclTableEntry> = sequence{
    for (e:CdclTableEntry in iterator())
    {
        if (e.level != 0)
        {
            break
        }
        yield(e)
    }
}

/**
 * If false, decisions will pick a random materials.getVariable and assign it to True.
 * If true, a materials.getVariable will be picked from the clauseSets activityHeap,
 * which prefers variables that occur in many conflicts and this materials.getVariable
 * will be assigned to the opposite that it was before
 */
const val useVsids:Boolean = true

/**
 * like in Chaff, all variables activities are halved every 256 conflicts
 */
const val conflictNumberForActivityDecay:Int = 256

/**
 * To not spend too much time with reordering, the reordering of the heap is only done every couple of conflicts
 */
const val conflictNumberForActivityReordering = 17

/**
 * increments with every conflict to trigger activity decay and reordering
 */
var conflictCounter:Int = 0


/**
 * Removes all entries with or below the given level and
 * returns a list of all variables that were unset
 */
fun CdclTable.backtrackTo(untilLevel: Int): List<Variable>
{
    fun allBelowLevel(entry:CdclTableEntry):Boolean = entry.level > untilLevel

    val retu:MutableList<Variable> = mutableListOf()

    for(x in this.filter {allBelowLevel(it)}.map {it.affectedVariable })
    {
        x.setTo(VariableSetting.Unset)
        retu.add(x)
    }

    this.removeAll { allBelowLevel(it) }
    return retu
}


/**
 * A resolvent is a materials.Clause based on a conflict in the CDCL algorithm which is
 * added to the clauseset to eventually directly find a solution
 *
 * Resolvents lead to knowledge about the given formula by finding decided
 * variablesettings that lead to the conflict.
 */
typealias Resolvent = MutableMap<Variable,Boolean>
fun makeResolvent():Resolvent = mutableMapOf()
fun makeResolvent(c: Clause):Resolvent = mutableMapOf(pairs=c.literals)
fun Resolvent.resolve(other: Clause, v: Variable) {
    this.resolve(makeResolvent(other),v)
}
/**
 * integrates the given resolvent, which is the reason for the given materials.getVariable
 * into this resolvent
 */
fun Resolvent.resolve(other: Resolvent,v: Variable) {
    this.remove(v)
    this.putAll(other.filter { it.key != v })
}
/**
 * returns any key in the resolvent, or null, if the resolvent is empty
 */
fun Resolvent.getAnyVariable(): Variable? =
        when (this.isEmpty()) {
            true -> null
            false -> this.keys.first()
        }


sealed class Reason
{
    class InUnitClause(c: Clause):Reason()
    {
        val reasonClause: Clause = c
    }

    object Decision : Reason()

    override fun toString(): String =
            when (this) {
                is InUnitClause -> "InUnitClause ("+this.reasonClause.toString()+")"
                is Decision -> "Decision"
            }
}

fun cdclSAT(clauseSet: ClauseSet):Boolean
{
    cdclSolve(clauseSet)

    return clauseSet.isFulfilled
}

//fun cdclSolve(s: String) = cdclSolve(materials.ClauseSetWatchedLiterals(s))
fun cdclSAT(s:String) = cdclSAT(ClauseSetWatchedLiterals(s))

fun cdclSolve(toSolve: ClauseSet, variablePriorityQueue:Map<Variable,Boolean>? = null): CdclTable {
    var level = 0
    val table : CdclTable = mutableListOf()
    val candidateIterator:Iterator<Map.Entry<Variable, Boolean>>? = variablePriorityQueue?.iterator()

    var previouslyAssignedVariable:Variable? = null

    while (true)
    {
        val units:List<Pair<Literal, Clause>> = toSolve.getAndSetUnitsWithReason(previouslyAssignedVariable)
        previouslyAssignedVariable = null

        if (units.isNotEmpty()) {
            table.addAll(units.map {
                unit ->  CdclTableEntry(
                    level,
                    unit.first.first,
                    unit.first.second,
                    Reason.InUnitClause(unit.second))})
            if (toSolve is ClauseSetWatchedLiterals) {
                units.map {it.first.variable }.forEach{
                    toSolve.updateWatchedLiterals(v=it)}
            }
            continue
        }


        if(toSolve.isEmpty)
        {
            previouslyAssignedVariable = null
            //a conflict occurred
            conflictCounter++
            conflictCounter %= conflictNumberForActivityDecay*conflictNumberForActivityReordering
            if (conflictCounter % conflictNumberForActivityDecay == 0) {
                toSolve.getPresentVariables().forEach { it.activity /= 2f }
            }
            if (toSolve is ClauseSetWatchedLiterals) {
                toSolve.resetAllWatchedLiterals()
            }
            assert { !toSolve.isFulfilled }
            if (level == 0) {
                return table //unresolvable conflict -> UNSAT
            }


            //the empty clause that is being evaluated, to learn a new clause
            val emptyClause: Clause = toSolve.getEmptyClause()!!
            // a set of (variables+materials.getPredicate) which is resolved with other reason clauses
            // prefixed variables which are set by decision are regularly extracted, until
            // resolvent is empty

            val resolvent:Resolvent = makeResolvent(emptyClause)
            //a variablesSet which is learned at the end
            val decidedConflictingVars:Resolvent = makeResolvent()//takes the decided variables out of the resolvent
            while (resolvent.isNotEmpty()) {
                val curDecidedVars:Map<Variable,Boolean> = resolvent.filter{
                    table.findReason(it.key) is Reason.Decision}
                decidedConflictingVars.putAll(curDecidedVars)
                for (dec in curDecidedVars) resolvent.remove(dec.key) // no removeAll ?

                //get any materials.getVariable from resolvent. If its empty the loop can be
                //ended
                val unitVar: Variable = resolvent.getAnyVariable() ?: break //"elvis operator"
                val reason:Reason = table.findReason(unitVar)!!
                assert{ reason is Reason.InUnitClause }
                if(reason is Reason.InUnitClause)
                    resolvent.resolve(reason.reasonClause,unitVar)
            }
            if (decidedConflictingVars.isEmpty()) {
                //conflict has no decided reason, so tautologically unsatisfiable
                return table
            }
            val resolventClause: Clause =
                    when (toSolve) {
                        is ClauseSetWatchedLiterals -> ClauseWatchedLiterals(decidedConflictingVars)
                        else -> Clause(decidedConflictingVars) //no other subclass
                    }
            toSolve.addResolvent(resolventClause)
            level--
            val affectedVariables = table.backtrackTo(level)
            //explicitely unset variables, this will also reset watched literals
            toSolve.resetVars(affectedVariables)

            //increase activity for conflict variables
            resolventClause.literals.forEach { it.first.activity++ }
            if (conflictCounter % conflictNumberForActivityReordering == 0) {
                toSolve.reorderActivityHeap()
            }
        }
        else if (toSolve.isFulfilled) {
            return table //found solution -> SAT
        }
        else { //do decision
            level++
            //always set false, let true come through learned clauses
            //getAnyFreeVariable mustnt be null, since if all variables
            //where set, the clauseSet would be SAT OR UNSAT
            var decidedVariable: Variable? = null

            //special for candidate/intersection backbone calculation
            //if candidates are present
            if (candidateIterator != null)
            {
                while (decidedVariable == null && candidateIterator.hasNext())
                {
                    val curCandidate = candidateIterator.next()
                    if (!curCandidate.key.isUnset) {
                        continue
                    } else {
                        decidedVariable = curCandidate.key
                        //note that
                        decidedVariable.setTo(curCandidate.value)
                    }
                }
            }

            //else: if no candidates exist (anymore) or none are supposed to be used
            // default to using any free materials.getVariable
            if(decidedVariable == null){
                if(useVsids)
                {
                    decidedVariable = toSolve.makeVsidsAssignment()
                }else{
                    decidedVariable = toSolve.getAnyFreeVariable()!!
                    decidedVariable.setTo(decisionVariableSetting)
                }
            }


            if (toSolve is ClauseSetWatchedLiterals) {
                toSolve.updateWatchedLiterals(decidedVariable)
            }
            table.add(CdclTableEntry(level,decidedVariable,decidedVariable.boolSetting!!,Reason.Decision))
            if (toSolve is ClauseSetWatchedLiterals &&
                ClauseWatchedLiterals.activeWLIterationScheme == WatchedLiteralIterationScheme.ToMiddle) {
                toSolve.resetAllWatchedLiterals()
            }
            previouslyAssignedVariable = decidedVariable
        }
    }
}

private var decisionVariableSetting: VariableSetting = VariableSetting.True

fun invertDecisionVariableSetting() {
    decisionVariableSetting = decisionVariableSetting.getOpposite()

}

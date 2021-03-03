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
 * Returns all variables that were set without a decision (except those that
 * were reverted due to conflicts).
 * If multiple SAT solutions are possible then the returned variables
 * have the same setting in all of those.
 * Note that some tautological variablesettings might not be included, if it
 * was guessed correctly initially
 *
 * Note that a set of variables might be returned independent of whether the clauseSet
 * is actually satisfiable
 */
fun CdclTable.getUnitVariables():Set<Literal> =
        this.filter { it.level == 0 }.map { Pair(it.affectedVariable,it.value) }.toSet()

/**
 * Removes all entries with or below the given level and
 * returns a list of all variables that were unset
 */
fun CdclTable.backtrackTo(untilLevel: Int): List<Variable>
{
    fun allBelowLevel(entry:CdclTableEntry):Boolean = entry.level > untilLevel

    var retu:MutableList<Variable> = mutableListOf()

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

fun cdclSolve(clauseSet: ClauseSet, variablePriorityQueue:Map<Variable,Boolean>? = null): CdclTable {
    var level = 0
    val table : CdclTable = mutableListOf()
    val candidateIterator:Iterator<Map.Entry<Variable, Boolean>>? = variablePriorityQueue?.iterator()

    while (true) {
        val units = clauseSet.getAndSetUnitsWithReason()

        if (units.isNotEmpty()) {
            table.addAll(units.map {
                unit ->  CdclTableEntry(
                    level,
                    unit.first.first,
                    unit.first.second,
                    Reason.InUnitClause(unit.second))})
            if (clauseSet is ClauseSetWatchedLiterals) {
                units.map {it.first.variable }.forEach{
                    clauseSet.updateWatchedLiterals(v=it)}
            }
            continue
        }


        if(clauseSet.isEmpty)
        {
            //a conflict occurred
            conflictCounter++
            conflictCounter %= conflictNumberForActivityDecay*conflictNumberForActivityReordering
            if (conflictCounter % conflictNumberForActivityDecay == 0) {
                clauseSet.getPresentVariables().forEach { it.activity /= 2f }
            }
            if (clauseSet is ClauseSetWatchedLiterals) {
                clauseSet.resetAllWatchedLiterals()
            }
            assert { !clauseSet.isFulfilled }
            if (level == 0) {
                return table //unresolvable conflict -> UNSAT
            }


            //the empty clause that is being evaluated, to learn a new clause
            val emptyClause: Clause = clauseSet.getEmptyClause()!!
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
                    when (clauseSet) {
                        is ClauseSetWatchedLiterals -> ClauseWatchedLiterals(decidedConflictingVars)
                        else -> Clause(decidedConflictingVars) //no other subclass
                    }
            clauseSet.addResolvent(resolventClause)
            level--
            val affectedVariables = table.backtrackTo(level)
            //explicitely unset variables, this will also reset watched literals
            clauseSet.resetVars(affectedVariables)

            //increase activity for conflict variables
            resolventClause.literals.forEach { it.first.activity++ }
            if (conflictCounter % conflictNumberForActivityReordering == 0) {
                clauseSet.reorderActivityHeap()
            }
        }
        else if (clauseSet.isFulfilled) {
            return table //found solution -> SAT
        }
        else { //do decision
            level++
            //always set false, let true come through learned clauses
            //getAnyFreeVariable mustnt be null, since if all variables
            //where set, the clauseSet would be SAT OR UNSAT
            var explicitelySetVar: Variable? = null

            //special for candidate/intersection backbone calculation
            //if candidates are present
            if (candidateIterator != null)
            {
                while (explicitelySetVar == null && candidateIterator.hasNext())
                {
                    val curCandidate = candidateIterator.next()
                    if (!curCandidate.key.isUnset) {
                        continue
                    } else {
                        explicitelySetVar = curCandidate.key
                        //note that
                        explicitelySetVar.setTo(curCandidate.value)
                    }
                }
            }

            //else: if no candidates exist (anymore) or none are supposed to be used
            // default to using any free materials.getVariable
            if(explicitelySetVar == null){
                if(useVsids)
                {
                    explicitelySetVar = clauseSet.makeVsidsAssignment() //TODO get this to work
                }else{
                    explicitelySetVar = clauseSet.getAnyFreeVariable()!!
                    explicitelySetVar.setTo(decisionVariableSetting)
                }
            }
            explicitelySetVar


            if (clauseSet is ClauseSetWatchedLiterals) {
                clauseSet.updateWatchedLiterals(explicitelySetVar)
            }
            table.add(CdclTableEntry(level,explicitelySetVar,explicitelySetVar.boolSetting!!,Reason.Decision))
            if (clauseSet is ClauseSetWatchedLiterals && ClauseWatchedLiterals.activeWLIterationScheme == WatchedLiteralIterationScheme.ToMiddle) {
                clauseSet.resetAllWatchedLiterals()
            }
        }
    }
}

private var decisionVariableSetting: VariableSetting = VariableSetting.True

fun invertDecisionVariableSetting() {
    decisionVariableSetting = decisionVariableSetting.getOpposite()

}

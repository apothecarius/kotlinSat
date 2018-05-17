import java.security.KeyStore

data class CdclTableEntry(
        val level:Int,
        val affectedVariable:Variable,
        val value:Boolean,
        val reason:Reason)

typealias CdclTable = MutableList<CdclTableEntry>
fun CdclTable.findReason(forVar: Variable):Reason? =
        this.find { it:CdclTableEntry -> it.affectedVariable == forVar }?.reason

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
        this.filter { it.level == 0 }.map { it -> Pair(it.affectedVariable,it.value) }.toSet()

/**
 * Removes all entries with or below the given level and
 * returns a list of all variables that were unset
 */
fun CdclTable.backtrackTo(untilLevel: Int): List<Variable> {
    var retu:MutableList<Variable> = mutableListOf()
    fun allBelowLevel(entry:CdclTableEntry):Boolean = entry.level > untilLevel
    this.filter { it:CdclTableEntry -> allBelowLevel(it)}.map {
        it -> it.affectedVariable }.forEach {
        it:Variable -> it.setTo(VariableSetting.Unset);retu.add(it)}

    this.removeAll { allBelowLevel(it) }
    return retu
}

fun CdclTable.print(){
    for (e: CdclTableEntry in this) {
        println(e.level.toString() + "\t"+e.affectedVariable.id +
                "\t "+e.value + "\t "+e.reason)
    }
}

/**
 * A resolvent is a Clause based on a conflict in the CDCL algorithm which is
 * added to the clauseset to eventually directly find a solution
 *
 * Resolvents lead to knowledge about the given formula by finding decided
 * variablesettings that lead to the conflict.
 */
typealias Resolvent = MutableMap<Variable,Boolean>
fun makeResolvent():Resolvent = mutableMapOf()
fun makeResolvent(c:Clause):Resolvent = mutableMapOf<Variable,Boolean>(pairs=*c.literals)
fun Resolvent.resolve(other: Clause, v: Variable) {
    this.resolve(makeResolvent(other),v)
}
/**
 * integrates the given resolvent, which is the reason for the given variable
 * into this resolvent
 */
fun Resolvent.resolve(other: Resolvent,v:Variable) {
    this.remove(v)
    if(other != null)
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


open class Reason private constructor ()
{
    class InUnitClause(c:Clause):Reason()
    {
        val reasonClause:Clause = c
    }
    class Decision:Reason()

    override fun toString(): String =
            when (this) {
                is InUnitClause -> "InUnitClause ("+this.reasonClause.toString()+")"
                is Decision -> "Decision"
                else -> "fail"
            }
}

fun cdclSAT(clauseSet:ClauseSet):Boolean
{
    val table = cdclSolve(clauseSet)

    return clauseSet.isFulfilled
}

fun cdclSolve(clauseSet: ClauseSet): CdclTable {
    var level:Int = 0
    val table : CdclTable = mutableListOf<CdclTableEntry>()

    while (true) {
        val units = clauseSet.getAndSetUnitsWithReason()

        if (!units.isEmpty()) {
            table.addAll(units.map {
                unit ->  CdclTableEntry(
                    level,
                    unit.first.first,
                    unit.first.second,
                    Reason.InUnitClause(unit.second))})
            if (clauseSet is ClauseSetWatchedLiterals) {
                units.map { it -> it.first.variable }.forEach{
                    clauseSet.updateWatchedLiterals(v=it)}
            }
            continue
        }


        if(clauseSet.isEmpty){
            if (clauseSet is ClauseSetWatchedLiterals) {
                clauseSet.resetAllWatchedLiterals()
            }
            assert( !clauseSet.isFulfilled )
            if (level == 0) {
                if (verbose) {
                    println(clauseSet.toString()+" error in "+
                            clauseSet.getEmptyClause().toString()+" -> UNSAT")
                    table.print()
                }
                return table //unresolvable conflict -> UNSAT
            }


            //the empty clause that is being evaluated, to learn a new clause
            val emptyClause:Clause = clauseSet.getEmptyClause()!!
            // a set of (variables+predicate) which is resolved with other reason clauses
            // prefixed variables which are set by decision are regularly extracted, until
            // resolvent is empty
            if (verbose) {
                println("Conflict in "+emptyClause+" , doing backtrack")
                table.print()
            }
            var resolvent:Resolvent = makeResolvent(emptyClause)
            //a variablesSet which is learned at the end
            var decidedConflictingVars:Resolvent = makeResolvent()//takes the decided variables out of the resolvent
            while (!resolvent.isEmpty()) {
                val curDecidedVars:Map<Variable,Boolean> = resolvent.filter{
                    table.findReason(it.key) is Reason.Decision}
                decidedConflictingVars.putAll(curDecidedVars)
                for (dec in curDecidedVars) resolvent.remove(dec.key) // no removeAll ?

                //get any variable from resolvent. If its empty the loop can be
                //ended
                var unitVar:Variable = resolvent.getAnyVariable() ?: break //"elvis operator"
                val reason:Reason = table.findReason(unitVar)!!
                assert( reason is Reason.InUnitClause)
                if(reason is Reason.InUnitClause)
                    resolvent.resolve(reason.reasonClause,unitVar)
            }
            if (decidedConflictingVars.isEmpty()) {
                //conflict has no decided reason, so tautologically unsatisfiable
                if (verbose) {
                    println("Found an unresolvable conflict -> UNSAT")
                }
                return table
            }
            val resolventClause:Clause =
                    when (clauseSet) {
                        is ClauseSetWatchedLiterals -> ClauseWatchedLiterals(decidedConflictingVars)
                        is ClauseSet -> Clause(decidedConflictingVars)
                        else -> null //syntactically necessary
                    }!!
            if (verbose) {
                println("Learning: "+resolventClause)
            }
            clauseSet.addResolvent(resolventClause)
            level--
            val affectedVariables = table.backtrackTo(level)
            //explicitely unset variables, this will also reset watched literals
            clauseSet.resetVars(affectedVariables)

        }
        else if (clauseSet.isFulfilled) {

            if (verbose) {
                println("SAT")
                table.print()
            }
            return table //found solution -> SAT
        }
        else { //do decision
            level++
            //always set false, let true come through learned clauses
            //getAnyFreeVariable mustnt be null, since if all variables
            //where set, the clauseSet would be SAT OR UNSAT
            val explicitelySetVar:Variable = clauseSet.getAnyFreeVariable()!!
            explicitelySetVar.setTo(decisionVariableSetting)
            if (clauseSet is ClauseSetWatchedLiterals) {
                clauseSet.updateWatchedLiterals(explicitelySetVar)
            }
            table.add(CdclTableEntry(level,explicitelySetVar,explicitelySetVar.boolSetting!!,Reason.Decision()))
            if (clauseSet is ClauseSetWatchedLiterals && activeWLIterationScheme == WatchedLiteralIterationScheme.ToMiddle) {
                clauseSet.resetAllWatchedLiterals()
            }
        }
    }
}

private var decisionVariableSetting:VariableSetting = VariableSetting.False

fun invertDecisionVariableSetting() {
    decisionVariableSetting = decisionVariableSetting.getOpposite()

}
fun setDecisionVariableSetting(v: Boolean) {
    decisionVariableSetting = when (v) {
        true -> VariableSetting.True
        false -> VariableSetting.False

    }
}
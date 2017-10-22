
data class CdclTableEntry(val level:Int,val affectedVariable:Variable, val value:Boolean, val reason:Reason)

typealias CdclTable = MutableList<CdclTableEntry>
fun CdclTable.findReason(forVar: Variable):Reason? =
        this.find { it:CdclTableEntry -> it.affectedVariable == forVar }?.reason

/**
 *
 */
fun CdclTable.backtrackTo(untilLevel: Int): Unit {
    fun allBelowLevel(entry:CdclTableEntry):Boolean = entry.level >= untilLevel
    this.filter { it:CdclTableEntry -> it.level >= untilLevel}.forEach {it:CdclTableEntry -> it.affectedVariable.setTo(VariableSetting.Unset) }
    this.removeAll { allBelowLevel(it) }
}
fun CdclTable.print():Unit{
    for (e: CdclTableEntry in this) {
        println(e.level.toString() + "\t"+e.affectedVariable.id + "\t "+e.value + "\t "+e.reason)
    }
}
typealias Resolvent = MutableMap<Variable,Boolean>
fun makeResolvent():Resolvent = mutableMapOf()
fun makeResolvent(c:Clause):Resolvent = mutableMapOf<Variable,Boolean>(pairs=*c.factors.toTypedArray())
fun Resolvent.resolve(other: Clause, v: Variable): Unit {
    this.resolve(makeResolvent(other),v)
}
fun Resolvent.resolve(other: Resolvent,v:Variable): Unit {
    this.remove(v)
    if(other != null)
        this.putAll(other.filter { it.key != v })
}


//typealias Resolvent = MutableMap<Variable,Boolean>

open class Reason private constructor ()
{
    class InUnitClause(c:Clause):Reason()
    {
        public val reasonClause:Clause = c
    }
    class Decision():Reason()
}

fun cdclSAT(clauseSet: ClauseSet): Boolean {
    var level:Int = 0
    val table : CdclTable = mutableListOf<CdclTableEntry>()

    while (true) {
        table.addAll(clauseSet.getAndSetUnitsWithReason().map {
            unit ->  CdclTableEntry(
                level,
                unit.first.first,
                unit.first.second,
                Reason.InUnitClause(unit.second))})
        if(clauseSet.isEmpty){
            if (level == 0) {
                return false //unresolvable conflict -> UNSAT
            }
            //the empty clause that is being evaluated, to learn a new clause
            val emptyClause:Clause = clauseSet.getEmptyClause()!!
            // a set of (variables+predicate) which is resolved with other reason clauses
            // prefixed variables which are set by decision are regularly extracted, until
            // resolvent is empty
            var resolvent:Resolvent = makeResolvent(emptyClause)
            //a variablesSet which is learned at the end
            var decidedConflictingVars:Resolvent = makeResolvent()//takes the decided variables out of the resolvent
            while (!resolvent.isEmpty()) {
                val curDecidedVars:Map<Variable,Boolean> = resolvent.filter{table.findReason(it.key) is Reason.Decision}
                decidedConflictingVars.putAll(curDecidedVars)
                for (dec in curDecidedVars) resolvent.remove(dec.key) // no removeAll ?

                if (resolvent.isEmpty()) { // kann weg
                    break
                }

                //get any variable from resolvent // TODO check if there is ANY other way
                var unitVar:Variable? = null
                for (v in resolvent) {
                    unitVar = v.key
                    break
                }
                if(unitVar == null)
                    break
                val reason:Reason = (table.findReason(unitVar)!!)
                assert( reason is Reason.InUnitClause)
                if(reason is Reason.InUnitClause)
                    resolvent.resolve(reason.reasonClause,unitVar)
                else
                    assert(false)
            }
            val resolventClause:Clause = Clause(decidedConflictingVars)
            println(resolventClause)
            clauseSet.addResolvent(resolventClause)
            level--
            table.backtrackTo(level)
        }
        else if (clauseSet.isFulfilled) {
            table.print()
            return true //found solution -> SAT
        }
        else {
            level++
            //always set false, let true come through learned clauses
            //getAnyFreeVariable mustnt be null, since if all variables
            //where set, the clauseSet would be SAT OR UNSAT
            val explicitelySetVar:Variable = clauseSet.getAnyFreeVariable()!!
            explicitelySetVar.setTo(VariableSetting.True)
            table.add(CdclTableEntry(level,explicitelySetVar,explicitelySetVar.boolSetting!!,Reason.Decision()))
        }
    }


}
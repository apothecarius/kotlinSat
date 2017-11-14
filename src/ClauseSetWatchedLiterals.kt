import kotlin.coroutines.experimental.buildSequence

/**
 * This class extends ordinary clauses to have watched literals, which
 * dramatically improves performance of unit propagation
 *
 * Determining whether a clause is satisfied, empty, unit or neither, as well as
 * returning the unit literal can be done in O(1)
 *
 * This O(1) only counts in most cases. The watched literals are reset when backtracking
 * occurs
 */
class ClauseSetWatchedLiterals(c: Array<ClauseWatchedLiterals>) : ClauseSet(c.map { it as Clause }.toTypedArray()) {

    constructor(cs: String) : this(cs, VariableSet())

    private constructor(cs:String,vs:VariableSet)  :
            this(cs.split(delimiters="&").
                    map { c:String -> ClauseWatchedLiterals(c,vs) }.toTypedArray())


    /**
     * stores for every variable the occurences in clauses
     * the map itself is not mutable, because no new variables can pop up,
     * but new clauses can be created
     */
    private var occurences : Map<Variable,MutableSet<ClauseWatchedLiterals>>
    init {
        var mutableOccurences:MutableMap<Variable,MutableSet<ClauseWatchedLiterals>> = mutableMapOf()
        for (c: ClauseWatchedLiterals in this.clauses.map { it -> it as ClauseWatchedLiterals }) {
            for (v: Variable in c.literals.map { it.variable }) {
                var occurenceSet: MutableSet<ClauseWatchedLiterals>? = mutableOccurences.get(v)
                if (occurenceSet == null) {
                    occurenceSet = mutableSetOf()
                    occurenceSet.add(c)
                    mutableOccurences.put(v, occurenceSet)
                } else {
                    occurenceSet.add(c)
                }
            }
        }

        occurences = mutableOccurences.toMap()
    }

    override fun addResolvent(c: Clause) {
        super.addResolvent(c)
        val c = c as ClauseWatchedLiterals
        for (l: Variable in c.literals.map { it ->it.variable }) {
            //the entry must exist, because the variable is known
            this.occurences[l]!!.add(c)
        }
    }

    override fun getPresentVariables(): Sequence<Variable> = buildSequence {
        for (v: Variable in occurences.keys) {
            yield(v)
        }
    }

    override fun getAndSetUnitsWithReason(): List<Pair<Literal, Clause>> {
        var retu:MutableList<Pair<Literal, Clause>> = mutableListOf()

        do {
            val directUnits = super.getAndSetUnitsWithReason()
            for (unit in directUnits) {
                retu.add(unit)
                val activeVar: Variable = unit.first.first
                this.updateWatchedLiterals(activeVar)
            }
        }while(! directUnits.isEmpty())

        return retu
    }

    fun updateWatchedLiterals(v:Variable):Unit
    {
        var occi = this.occurences[v]
        occi?.forEach{it.updateWatchedLiterals(v)}
    }
    override fun resetVars(vs : List<Variable>):Unit
    {
        super.resetVars(vs)

        var affectedClauses = vs.map { it -> this.occurences[it] }.
                filter { it != null }.flatMap { it -> it!! }.distinct()

        for (c: ClauseWatchedLiterals in affectedClauses) {
            c.resetWatchedLiterals()
        }
    }

    fun resetAllWatchedLiterals() {
        for (klaus: Clause in this.clauses) {
            (klaus as ClauseWatchedLiterals).resetWatchedLiterals()
        }
    }
}
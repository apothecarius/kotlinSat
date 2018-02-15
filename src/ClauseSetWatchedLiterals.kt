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

    constructor(toCopy: ClauseSetWatchedLiterals):this(toCopy.toString())
    {
        for (cvs: Literal in toCopy.getVariableSetting()) {
            this.findVar(cvs.variable.id)!!.setTo(cvs.second)
        }
    }


    private constructor(cs:String,vs:VariableSet)  :
            this(cs.split(delimiters="&").
                    map { c:String -> ClauseWatchedLiterals(c,vs) }.toTypedArray())

    private val clausesWL:List<ClauseWatchedLiterals>
        get() = this.clauses as List<ClauseWatchedLiterals>

    //TODO occurences pro Literal anstatt Variable
    /**
     * stores for every variable the occurences in clauses
     * the map itself is not mutable, because no new variables can pop up,
     * but new clauses can be created
     */
    private var occurences : Map<Variable,MutableSet<ClauseWatchedLiterals>>
    init {
        occurences = this.setupOccurences()
    }

    private fun setupOccurences():Map<Variable,MutableSet<ClauseWatchedLiterals>> {
        var mutableOccurences:MutableMap<Variable,MutableSet<ClauseWatchedLiterals>> = mutableMapOf()
        for (c: ClauseWatchedLiterals in this.clausesWL) {
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

        return mutableOccurences.toMap()
    }

    fun getLiteralOccurences(): Map<Literal, Set<ClauseWatchedLiterals>> {
        var retu = mutableMapOf<Literal, Set<ClauseWatchedLiterals>>()
        for (clausesWithVar in this.occurences) {
            for (prefix in arrayOf(true, false)) {
                val occurencesWithPrefix = clausesWithVar.value.filter {it ->
                    it.literals.filter {
                        it.predicate == prefix && it.variable ==  clausesWithVar.key}.isNotEmpty() }
                if (occurencesWithPrefix.isNotEmpty()) {
                    val literalKey:Literal = Pair(clausesWithVar.key,prefix)
                    retu.put(literalKey,occurencesWithPrefix.toSet())
                }
            }

        }
        return retu
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
        for (klaus in this.clausesWL) {
            klaus.resetWatchedLiterals()
        }
    }

    fun prepareWatchedLiteralsForImplicants() {
        //set a flag that lets the watched literals rest on fulfilled literals only
        ClauseWatchedLiterals.watchedLiteralsForUnitVariables = false
        //move the literals to the startpositions
        this.resetAllWatchedLiterals()
//        this.clausesWL.forEach { it.resetWatchedLiterals() }
    }


    fun getWatchedLiteralToClause():WatchedLiteralToClause {
        assert(! ClauseWatchedLiterals.watchedLiteralsForUnitVariables)
        var retu:WatchedLiteralToClause = WatchedLiteralToClause()

        for (clause in this.clausesWL) {
            for (lit: Literal in clause.getBothWatchedLiterals().toList().filterNotNull()) {
                retu.put(lit,clause)
            }
        }
        return retu
    }

    fun removeFalsyVariables() {
        this.clauses.forEach { it.filterFalsyLiterals() }
        this.setupOccurences()
        this.resetAllWatchedLiterals()
    }
    private fun findVar(id: VariableIdentifier): Variable? {
        return this.occurences.keys.find { it.id == id}
    }

    /**
     * Compares two clauseSets for their variable settings, and returns
     * true if equal
     */
    fun isSettingEqual(toCompare: ClauseSetWatchedLiterals): Boolean {
        for (v: Variable in this.occurences.keys) {
            val pendant:Variable = toCompare.findVar(v.id) ?: return false
            if(pendant.setting != v.setting)
                return false
        }
        return true
    }

}
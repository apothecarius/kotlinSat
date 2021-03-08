package materials

import support.assert

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
open class ClauseSetWatchedLiterals(c: Array<ClauseWatchedLiterals>) : ClauseSet(c.map { it as Clause }.toTypedArray()) {

    constructor(cs: String) : this(cs, VariableSet())
    constructor(cs: ClauseSetWatchedLiterals, vs: VariableSet) : this(cs.clausesWL.map { it -> ClauseWatchedLiterals(it,vs) }.toTypedArray())
    constructor(cs: ClauseSetWatchedLiterals, referVariables:Boolean) : this(cs,if(referVariables){
                VariableSet(cs.getPresentVariables())
    }else{
        VariableSet()
    })



    private constructor(cs:String,vs: VariableSet)  :
        this(cs.split("&").
                map { c:String -> ClauseWatchedLiterals(c,vs) }.toTypedArray())

    val clausesWL:List<ClauseWatchedLiterals>
    get() = this.getClauses() as List<ClauseWatchedLiterals>

    //TODO occurences pro materials.Literal anstatt materials.Variable
    /**
     * stores for every materials.getVariable the occurences in clauses
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


    override fun addResolvent(c: Clause) {
        super.addResolvent(c)
        val c = c as ClauseWatchedLiterals
        for (l: Variable in c.literals.map { it.variable }) {
            //the entry must exist, because the materials.getVariable is known
            this.occurences[l]!!.add(c)
        }
    }

    override fun getAndSetUnitsWithReason(mostRecentAssignment:Variable?):
            List<Pair<Literal, Clause>>
    {
        var retu:MutableList<Pair<Literal, Clause>> = mutableListOf()
        var retuVar:Variable? = mostRecentAssignment

        do {
            val directUnits = super.getAndSetUnitsWithReason(retuVar)
            for (unit in directUnits) {
                retu.add(unit)
                val activeVar: Variable = unit.first.first
                this.updateWatchedLiterals(activeVar)
            }
        }while(directUnits.isNotEmpty())

        return retu
    }

    fun updateWatchedLiterals(v: Variable):Unit
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


    fun removeFalsyVariables() {
        this.getClauses().forEach { it.filterFalsyLiterals() }
        this.setupOccurences()
        this.resetAllWatchedLiterals()
    }
    private fun findVar(id: VariableIdentifier): Variable? {
        return this.occurences.keys.find { it.id == id}
    }

    /**
     * Compares two clauseSets for their materials.getVariable settings, and returns
     * true if equal
     */
    fun isSettingEqual(toCompare: ClauseSetWatchedLiterals): Boolean {
        for (v: Variable in this.occurences.keys) {
            val pendant: Variable = toCompare.findVar(v.id) ?: return false
            if(pendant.setting != v.setting)
                return false
        }
        return true
    }
}


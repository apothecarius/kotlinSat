package materials

import algorithms.cdclSAT
import support.Heap
import support.assert

/**
 * A clauseset is the conjunction of multiple clauses
 * All clauses must be fulfilled for a clauseset to be fulfilled
 */
open class ClauseSet(c:Array<Clause>)
{
    private val clauses : MutableList<Clause> = c.toMutableList()
    private val activityHeap: Heap<Variable> = Heap(this.getPresentVariables())
    protected val occurences:Map<Variable,MutableList<Clause>> = this.getPresentVariables()
        .associateWith { mutableListOf() }

    //initialize literal activity with the number of occurences
    init{
        this.getPresentVariables().forEach { it.activity = 0f }
        this.clauses.forEach{ curClause ->
            curClause.literals.forEach{ curLit ->
                //initialize activity
                curLit.first.activity++

                //setup reverse lookup
                occurences[curLit.first]!!.add(curClause)
            }}
    }

    fun reorderActivityHeap() = this.activityHeap.reorder()

    /*
     * Pass an immutable reference
     */
    open fun getOccurencesLookup():Map<Variable,List<Clause>> = this.occurences

    fun makeVsidsAssignment(): Variable
    {
        //the function is called when there is an unassigned materials.getVariable
        //and variables with assignment are always considered "smaller"
        // changes update the materials.getVariable position
        var toAssign: Variable
        do{
            toAssign = this.activityHeap.pop()!!
        } while(!toAssign.isUnset)

        //assigned variables might be returned, have to be skipped
        assert { toAssign.isUnset }
        toAssign.setTo(!toAssign.previousSetting)
        return toAssign
    }

    /**
     * A materials.ClauseSet can be instantiated by passing a string containing a formula
     * a|b & c|d
     * The pipes (meaning an OR relation) bind stronger than the ampersand
     * (meaning a AND relation), whitespace can be added freely, brackets are
     * not supported
     */
    constructor(cs:String):this(cs, VariableSet()) //integrate the below into this constructor
    protected constructor(cs:String,vs: VariableSet)  :
            this(cs.split("&").map { c:String -> Clause(c,vs) }.toTypedArray())

    val isFulfilled : Boolean
        get() = clauses.all { a: Clause -> a.isSatisfied }
    val isEmpty : Boolean
        get() = clauses.any { a -> a.isEmpty }
    val isFresh: Boolean
        get() = this.getPresentVariables().all { it.isUnset }

    fun getClauses(): List<Clause> {
        return this.clauses
    }

    open fun addResolvent(c: Clause)
    {
        this.clauses.add(c)
        //also add it to the reverse lookup
        c.literals.map { it.first }.forEach { resolventsVar ->
            this.occurences[resolventsVar]!!.add(c)
        }
    }


    fun findUnsatClauses():Sequence<Clause>
    {
        val myClauses = this.clauses
        return sequence {
            myClauses.forEach { curClause ->
                if(curClause.isEmpty)
                    yield(curClause)
            }
        }
    }

    fun solve():Boolean
    {
        return cdclSAT(this)
    }

    open fun getPresentVariables(): Sequence<Variable> = sequence {
        //the variables that were already returned
        val metVars:MutableSet<Variable> = mutableSetOf()
        for (c: Clause in clauses)
        {
            for(v: Variable in c.literals.map { it.first })
            {
                if (metVars.contains(v)) {
                    continue
                } else {
                    metVars.add(v)
                    yield(v)
                }
            }
        }
    }


    /**
     * returns all variables that were set
     */
    fun setUnits(): List<Variable>
    {
        return this.getAndSetUnitsWithReason().map {it.first.first}
    }

    /**
     * Iterates over all clauses, looking for one in unit state and assigns the last unassigned materials.getVariable
     * @return all variables that were assigned in this way (that were unit propagated) and the reason clause
     * also the last assigned variable
     */
    open fun getAndSetUnitsWithReason(mostRecentAssignment:Variable? = null) :
            List<Pair<Literal, Clause>>
    {
        val retu:MutableList<Pair<Literal, Clause>> = mutableListOf()


        //as long as you find unit clauses
        val varsToPropagate:MutableList<Variable> = mutableListOf()
        if (mostRecentAssignment != null) {
            varsToPropagate.add(mostRecentAssignment)
        }

        var startException = mostRecentAssignment == null

        while(varsToPropagate.isNotEmpty() || startException)
        {
            startException = false

            //check all clauses for being empty or unit
            val clausesToCheck:MutableList<Clause> = if(varsToPropagate.isEmpty())
            {
                this.clauses
            }
            else
            {
                this.occurences[varsToPropagate.removeFirst()]!!
            }

            for(c : Clause in clausesToCheck)
            {
                if(c.isEmpty) {
                    return retu
                }

                val curUnit:Pair<Variable,Boolean>? = c.currentUnit
                if(curUnit != null)
                {
                    curUnit.first.setTo(when(curUnit.second){
                        true -> VariableSetting.True
                        false -> VariableSetting.False
                    })
                    varsToPropagate.add(curUnit.variable)
                    retu.add(Pair(curUnit, c))
                }
            }
        }
        return retu

    }

    fun getAnyFreeVariable(): Variable? = this.clauses.find {
        c: Clause -> c.freeVariable != null }?.freeVariable


    fun getEmptyClause(): Clause?
    {
        return this.clauses.find { c: Clause -> c.isEmpty }
    }

    open fun resetVars()
    {
        this.resetVars(this.getPresentVariables().toList())
    }
    open fun resetVars(vs : List<Variable>)
    {
        for(uv: Variable in vs)
        {
            uv.setTo(VariableSetting.Unset)
            this.activityHeap.add(uv)
        }

    }
    fun getVariableSetting():Set<Literal> =
            this.getPresentVariables().filter{ ! it.isUnset}.
                map { Pair(it,it.boolSetting!!) }.toSet()

    fun setTo(variableSettings: Set<Literal>) {
        for (e in variableSettings) {
            e.variable.setTo(e.predicate)
        }
    }

    override fun toString():String
    {
        return this.clauses.joinToString(separator = " & ") { it.toString() }
    }

    fun printVarSettings() {
        for (v: Variable in getPresentVariables()) {
            print(v.id + "->"+v.setting+" , ")
        }
        println()
    }

    /**
     * Caches present variables and gives a lookup by their identifier
     * TODO: If you add new variables, like Tseitin, then this lookup must be
     * cleared with invalidateVarnameLookup
     * ALTERNATIVELY assert that new variables are never added to a ClauseSet.
     * If you want to use Tseitin transformation, create a new formula object
     */
    private var varnameToVariable:Map<VariableIdentifier,Variable>? = null

    private fun invalidateVarnameLookup()
    {
        varnameToVariable = null
    }
    private fun setupVarnameLookup()
    {
        if(this.varnameToVariable == null)
            this.varnameToVariable = this.getPresentVariables().associateBy { it.id  }
    }


    fun findVariable(i: VariableIdentifier): Variable? {
        this.setupVarnameLookup()
        return this.varnameToVariable!![i]
    }


    /**
     * returns a multiple independent lists of clauses, that share their variables
     * For a fulfilling solution to this clauseSet, each of these lists of clauses
     * could be evaluated independently
     */
    fun separateClauses():List<List<Clause>> {

        val retu: MutableSet<FormulaGroup> = mutableSetOf()
        for (c: Clause in this.getClauses()) {
            val groups:List<FormulaGroup> = retu.filter { groupToCheck -> groupToCheck.first.any { //all groups where any materials.getVariable
                varToCheck -> c.literals.map { it.variable }.contains(varToCheck) }} //is contained in the variables of c

            if (groups.isEmpty()) {
                retu.add(FormulaGroup(c.literals.map { it.variable }.toMutableSet(), mutableListOf(c)))
            } else{
                //remove the found sets from retu, merge them and add that to retu
                retu.removeAll(groups)

                val occuringVars:Set<Variable> = groups.map { it.first }.fold(setOf(),
                        { acc: Set<Variable>, mutableSet: MutableSet<Variable> -> acc.union(mutableSet) }).
                        union(c.literals.map { it.variable })

                val associatedClauses: MutableSet<Clause> = groups.map { it.second.toSet() }.fold(setOf(),
                        { acc: Set<Clause>, mutableSet: Set<Clause> -> acc.union(mutableSet) }).toMutableSet()
                associatedClauses.add(c)
                retu.add(FormulaGroup(occuringVars.toMutableSet(), associatedClauses.toMutableList()))
            }
        }
        return retu.map { it.second }
    }
}
private typealias FormulaGroup = Pair<MutableSet<Variable>, MutableList<Clause>>
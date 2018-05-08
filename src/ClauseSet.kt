import kotlin.coroutines.experimental.buildSequence

/**
 * A clauseset is the conjunction of multiple clauses
 * All clauses must be fulfilled for a clauseset to be fulfilled
 */
open class ClauseSet(c:Array<Clause>)
{
    private val clauses : MutableList<Clause> = c.toMutableList()

    /**
     * A ClauseSet can be instantiated by passing a string containing a formula
     * a|b & c|d
     * The pipes (meaning an OR relation) bind stronger than the ampersand
     * (meaning a AND relation), whitespace can be added freely, brackets are
     * not supported
     */
    constructor(cs:String):this(cs,VariableSet()) //integrate the below into this constructor
    protected constructor(cs:String,vs:VariableSet)  :
            this(cs.split(delimiters="&").
                    map { c:String -> Clause(c,vs) }.toTypedArray())

    constructor(cs:ClauseSet) : this(cs.clauses.map { it -> Clause(it) }.toTypedArray())

    val isFulfilled : Boolean
        get() = clauses.all { a:Clause -> a.isSatisfied }
    val isEmpty : Boolean
        get() = clauses.any { a -> a.isEmpty }

    fun getClauses(): List<Clause> {
        return this.clauses
    }

    open fun addResolvent(c:Clause)
    {
        this.clauses.add(c)
    }

    open fun getPresentVariables(): Sequence<Variable> = buildSequence {
        //the variables that were already returned
        val metVars:MutableSet<Variable> = mutableSetOf()
        for (c: Clause in clauses) {
            for(v:Variable in c.literals.map { it -> it.first })
                if (metVars.contains(v)) {
                    continue
                } else {
                    metVars.add(v)
                    yield(v)
                }
        }
    }

    fun copyClauses(): MutableList<Clause> {
        var retu = mutableListOf<Clause>()
        retu.addAll(this.clauses)
        return retu
    }


    /**
     * returns all variables that were set
     */
    fun setUnits(): List<Variable>
    {
        return this.getAndSetUnitsWithReason().map { it -> it.first.first}
    }

    open fun getAndSetUnitsWithReason():List<Pair<Literal,Clause>>
    {
        var retu  = mutableListOf<Pair<Literal,Clause>>()

        //as long as you find unit clauses
        var foundSomething:Boolean = true
        while(foundSomething)
        {
            foundSomething = false
            //check all clauses for being empty or unit
            for(c : Clause in this.clauses)
            {
                if(c.isEmpty)
                    return retu

                var curUnit:Pair<Variable,Boolean>? = c.currentUnit
                if(curUnit != null)
                {
                    foundSomething = true
                    curUnit.first.setTo(when(curUnit.second){
                        true -> VariableSetting.True
                        false -> VariableSetting.False
                    })
                    retu.add(Pair(curUnit, c))
                }
            }
        }
        return retu

    }

    fun getAnyFreeVariable(): Variable? = this.clauses.find {
        c: Clause -> c.freeVariable != null }?.freeVariable


    fun getEmptyClause():Clause?
    {
        return this.clauses.find { c:Clause -> c.isEmpty }
    }

    /**
     * Sets any remaining variable to the passed parameter (defaulting to true)
     * This function requires the boolean formula to be fulfilled already, or it
     * will crash
     */
    fun fillModel(setting:Boolean = true) {
        assert(this.isFulfilled)
        while (true) {
            var freeVar:Variable = this.getAnyFreeVariable() ?: break
            freeVar.setTo(setting)
        }
    }

    open fun resetVars(){
        this.resetVars(this.getPresentVariables().toList())
    }
    open fun resetVars(vs : List<Variable>):Unit
    {
        for(uv:Variable in vs)
            uv.setTo(VariableSetting.Unset)
    }
    fun getVariableSetting():Set<Literal> =
            this.getPresentVariables().filter{ ! it.isUnset}.
                map { it -> Pair(it,it.boolSetting!!) }.toSet()

    fun setTo(variableSettings: Set<Literal>) {
        for (e in variableSettings) {
            e.variable.setTo(e.predicate)
        }
    }

    override fun toString():String
    {
        return this.clauses.map { it.toString() }.joinToString(separator=" & ")
    }

    fun printVarSettings(): Unit {
        val alreadyPrintedVars:MutableSet<Variable> = mutableSetOf()
        for (c: Clause in this.clauses) {
            for (v: Variable in c.literals.map { it.first }) {
                if (alreadyPrintedVars.contains(v)) {
                    continue;
                } else {
                    print(v.id + "->"+v.setting+" , ")
                    alreadyPrintedVars.add(v)
                }
            }
        }
        println()
    }

    fun printClauses(): Unit {
        for (c: Clause in this.clauses) {
            println(c)
        }
    }

    fun findVariable(i: VariableIdentifier): Variable? {
        return this.getPresentVariables().find { it.id == i }
    }


    /**
     * returns a multiple independent lists of clauses, that share their variables
     * For a fulfilling solution to this clauseSet, each of these lists of clauses
     * could be evaluated independently
     */
    fun separateClauses():List<List<Clause>> {

        var retu: MutableSet<FormulaGroup> = mutableSetOf()
        for (c: Clause in this.getClauses()) {
            var groups:List<FormulaGroup> = retu.filter {groupToCheck -> groupToCheck.first.any { //all groups where any variable
                varToCheck -> c.literals.map { it.variable }.contains(varToCheck) }} //is contained in the variables of c

            if (groups.isEmpty()) {
                retu.add(FormulaGroup(c.literals.map { it.variable }.toMutableSet(), mutableListOf(c)))
            } else{
                //remove the found sets from retu, merge them and add that to retu
                retu.removeAll(groups)

                val occuringVars:Set<Variable> = groups.map { it.first }.fold(setOf<Variable>(),
                        {acc: Set<Variable>, mutableSet: MutableSet<Variable> -> acc.union(mutableSet) }).
                        union(c.literals.map { it.variable })

                val associatedClauses: MutableSet<Clause> = groups.map { it.second.toSet() }.fold(setOf<Clause>(),
                        {acc: Set<Clause>, mutableSet: Set<Clause> -> acc.union(mutableSet) }).toMutableSet()
                associatedClauses.add(c)
                retu.add(FormulaGroup(occuringVars.toMutableSet(), associatedClauses.toMutableList()))

                //val toAdd:FormulaGroup = FormulaGroup(groups.map{it.first}.)



            }


        }

        return retu.map { it -> it.second }
    }
}
private typealias FormulaGroup = Pair<MutableSet<Variable>, MutableList<Clause>>
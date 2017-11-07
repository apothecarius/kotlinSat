
/**
 * A clauseset is the conjunction of multiple clauses
 * All clauses must be fulfilled for a clauseset to be fulfilled
 */
open class ClauseSet(c:Array<Clause>)
{
    protected var clauses : MutableList<Clause> = c.toMutableList()


    constructor(cs:String):this(cs,VariableSet()) //integrate the below into this constructor
    protected constructor(cs:String,vs:VariableSet)  :
            this(cs.split(delimiters="&").
                    map { c:String -> Clause(c,vs) }.toTypedArray())


    val isFulfilled : Boolean
        get() = clauses.all { a:Clause -> a.isSatisfied }
    val isEmpty : Boolean
        get() = clauses.any { a -> a.isEmpty }

    open fun addResolvent(c:Clause)
    {
        this.clauses.add(c)
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

    open fun resetVars(vs : List<Variable>):Unit
    {
        for(uv:Variable in vs)
            uv.setTo(VariableSetting.Unset)
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
                    println(v.id + " -> "+v.setting)
                    alreadyPrintedVars.add(v)
                }


            }
        }
    }

    fun printClauses(): Unit {
        for (c: Clause in this.clauses) {
            println(c)
        }
    }


}
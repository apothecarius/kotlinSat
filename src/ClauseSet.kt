
/**
 * A clauseset is the conjunction of multiple clauses
 * All clauses must be fulfilled for a clauseset to be fulfilled
 */
class ClauseSet(c:Array<Clause>)
{
    private var clauses : MutableList<Clause> = c.toMutableList()

    constructor(cs:String):this(cs,VariableSet())
    private constructor(cs:String,vs:VariableSet)  :
            this(cs.split(delimiters="&").
                    map { c:String -> Clause(c,vs) }.toTypedArray())


    val isFulfilled : Boolean
        get() = clauses.all { a:Clause -> a.isSatisfied }
    val isEmpty : Boolean
        get() = clauses.any { a -> a.isEmpty }

    fun addResolvent(c:Clause)
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

    fun getAndSetUnitsWithReason():List<Pair<Pair<Variable,Boolean>,Clause>>
    {
        var retu  = mutableListOf<Pair<Pair<Variable,Boolean>,Clause>>()

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

    fun getAnyFreeVariable():Variable?
    {
        return this.clauses.find { c:Clause -> c.freeVariable != null }?.freeVariable
    }
    fun getEmptyClause():Clause?
    {
        return this.clauses.find { c:Clause -> c.isEmpty }
    }

    fun dpllSAT():Boolean
    {
        val unitVars:List<Variable> = this.setUnits()
        if (this.isEmpty) {
            this.resetVars(unitVars)
            return false
        } else if (this.isFulfilled) {
            return true
        }

        //there must be any free variable, that is needs to
        //be set in a nontrivial way
        val freeVariable:Variable = this.getAnyFreeVariable()!!
        println(freeVariable)

        //try true
        freeVariable.setTo(VariableSetting.True)
        val workedWithTrue:Boolean = this.dpllSAT()
        if(workedWithTrue)
            return true
        //try false
        freeVariable.setTo(VariableSetting.False)
        val workedWithFalse:Boolean = this.dpllSAT()
        if (workedWithFalse) {
            return true
        }
        //the given setting of variables is not working
        this.resetVars(unitVars+freeVariable)
        println("didnt work")
        return false
    }

    fun resetVars(vs : List<Variable>):Unit
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
            for (v: Variable in c.factors.map { it.first }) {
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
/**
 * A Clause is a disjunction of multiple variables with or without a negation predicate
 */
class Clause constructor(disjunction : Array<Pair<Variable,Boolean>>)
{
    private var vars : Array<Variable> = disjunction.map { a -> a.first }.toTypedArray();
    private var predicates: Array<Boolean> = disjunction.map{ a -> a.second}.toTypedArray();

    constructor (c: String,knownVariables:VariableSet) :
            this(c.filter { cv: Char ->  cv != ' '}. //remove whitespace
                    split("|"). //split variables
                    map { v:String ->
                        if(v.startsWith("!")) //recognize negations
                            Pair(knownVariables.storeOrGet(v.substring(1)),false)
                        else{
                            Pair(knownVariables.storeOrGet(v),true)
                        }
                    }.toTypedArray())
    constructor(cs:Map<Variable,Boolean>) :  this(cs.map { it -> Pair(it.key,it.value) }.toTypedArray())

    val isUnit : Boolean
        get() =  ! this.isSatisfied && vars.count {v:Variable -> v.setting == VariableSetting.Unset  } == 1
    val isEmpty : Boolean
        get() = vars.zip(predicates, { a:Variable, b:Boolean -> a.isFalseWith(b)} ).all { wasFalse:Boolean -> wasFalse }
    val isSatisfied : Boolean
        get() = vars.zip(predicates, { a:Variable, b:Boolean -> a.isTrueWith(b)}).any { a->a }

    val currentUnit: Pair<Variable,Boolean>? get() {
        if(! this.isUnit)
            return null
        else
        {
            //findOnly would be nice to remove one loop
            val unitsIdx:Int? = this.vars.indexOfFirst { v -> v.setting == VariableSetting.Unset }
            return when(unitsIdx){
                null ->  null
                else ->  Pair(vars[unitsIdx],predicates[unitsIdx])
            }
        }
    }

    val freeVariable:Variable?
        get() = this.vars.find { a:Variable -> a.setting == VariableSetting.Unset}

    val factors = this.vars.zip(predicates)  //rename

    override fun toString():String
    {
        return this.vars.zip(this.predicates).
                map{it -> if(it.second){""}else{"!"}+it.first}.
                joinToString(separator = "|")
    }
}
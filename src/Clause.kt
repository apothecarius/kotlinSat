typealias Literal = Pair<Variable, Boolean>
val Literal.variable:Variable
        get() = this.first
val Literal.predicate:Boolean
        get() = this.second

//TODO implement watched literals

/**
 * A Clause is a disjunction of multiple variables with or without a negation predicate
 */
class Clause constructor(disjunction : Array<Pair<Variable,Boolean>>)
{
//    private var vars : Array<Variable> = disjunction.map { a -> a.first }.toTypedArray();
//    private var predicates: Array<Boolean> = disjunction.map{ a -> a.second}.toTypedArray();
    var literals : Array<Literal> = disjunction

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
        get() =  ! this.isSatisfied && literals.count {l:Literal -> l.variable.setting == VariableSetting.Unset  } == 1
    val isEmpty : Boolean
        get() = literals.all {it.variable.isFalseWith(it.predicate)}
    val isSatisfied : Boolean
        get() = this.literals.any{it.variable.isTrueWith(it.predicate)}

    val currentUnit: Pair<Variable,Boolean>? get() {
        if(! this.isUnit)
            return null
        else
        {
            //findOnly would be nice to remove one loop
            return this.literals.first { it.variable.setting == VariableSetting.Unset}
        }
    }

    val freeVariable:Variable?
        get() = this.literals.find { it.variable.setting == VariableSetting.Unset}?.variable



    override fun toString():String
    {
        return this.literals.
                map{it -> if(it.predicate){""}else{"!"}+it.variable}.
                joinToString(separator = "|")
    }
}
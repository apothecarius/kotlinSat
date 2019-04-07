typealias Literal = Pair<Variable, Boolean>
val Literal.variable:Variable
        get() = this.first
val Literal.predicate:Boolean
        get() = this.second

fun Literal.becomesTrue():Boolean {
    return this.variable.isTrueWith(this.predicate)
}
fun Literal.becomesFalse():Boolean{
    return this.variable.isFalseWith(this.predicate)
}
val Literal.isUnset: Boolean get() =
    this.variable.setting == VariableSetting.Unset
val Literal.writeShort:String get() = (if(!this.predicate) "!" else "") + this.variable.id


fun codeToLiteralSet(c: String,knownVariables: VariableSet): Array<Literal> =
    c.filter { cv: Char ->  cv != ' '}. //remove whitespace
            split("|"). //split variables
            map { v:String ->
                if(v.startsWith("!")) //recognize negations
                    Pair(knownVariables.storeOrGet(v.substring(1)),false)
                else{
                    Pair(knownVariables.storeOrGet(v),true)
                }
            }.toTypedArray()

/**
 * A Clause is a disjunction of multiple variables with or without a negation predicate
 */
open class Clause constructor(disjunction : Array<Literal>)
{
//    private var vars : Array<Variable> = disjunction.map { a -> a.first }.toTypedArray();
//    private var predicates: Array<Boolean> = disjunction.map{ a -> a.second}.toTypedArray();
    var literals : Array<Literal> = disjunction.sortedBy { it.variable.id }.toTypedArray()

    constructor(c: Clause) : this(c.literals.map { it:Literal -> Literal(Variable(it.variable),it.predicate) }.toTypedArray())

    constructor(l: Literal) : this(arrayOf<Literal>(l))
    constructor (c: String,knownVariables:VariableSet):this(codeToLiteralSet(c,knownVariables))
    constructor(cs:Map<Variable,Boolean>) : this(
            cs.map { it -> Pair(it.key,it.value) }.toTypedArray())

    open val isUnit : Boolean
        get() =  ! this.isSatisfied && literals.count {l:Literal -> l.variable.setting == VariableSetting.Unset  } == 1
    open val isEmpty : Boolean
        get() = literals.all {it.becomesFalse()}
    open val isSatisfied : Boolean
        get() = this.literals.any{it.becomesTrue()}

    open val currentUnit: Pair<Variable,Boolean>? get() {
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

    open fun filterFalsyLiterals() {
        this.literals = this.literals.filter { it.becomesTrue() }.toTypedArray()
    }
}
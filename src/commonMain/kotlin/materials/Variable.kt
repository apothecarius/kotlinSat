package materials

import support.assert

typealias VariableIdentifier = String
enum class VariableSetting {True,False,Unset}
fun VariableSetting.getOpposite(): VariableSetting
{
    return when(this){
        VariableSetting.True -> VariableSetting.False
        VariableSetting.False -> VariableSetting.True
        VariableSetting.Unset -> VariableSetting.Unset
    }


}

fun makeVarIds(numVars: Int): List<VariableIdentifier> {
    var retu = mutableListOf<VariableIdentifier>()
    for (i: Int in 64..64 + numVars) {
        var ic: VariableIdentifier = i.toString()
        assert{ ic.isNotBlank() }
        retu.add(ic)
    }
    return retu
}

class Variable constructor(c: VariableIdentifier) : Comparable<Variable> {
    constructor(v: Variable) : this(v.id) {
        this.setTo(v.setting)
    }


    /**
     * Increases when this materials.getVariable is involved with a conflict and decreases over time
     * Is used to determine which materials.getVariable should be assigned to
     */
    var activity: Float = 0f

    var id: VariableIdentifier = c

    init {
        assert{ id.isNotBlank() }
    }

    var setting: VariableSetting = VariableSetting.Unset

    /**
     * Stores to previous actual assignment. This way subsequent assignments can do the opposite
     * TODO initialize to the least occuring phase in the formula, so that the first assignment is optimal
     */
    var previousSetting: Boolean = false

    /**
     * Sets the variables state (false,true,unset)
     * Note that if you use watched Literals, then you need to update
     * them in all clauseSets that use this materials.getVariable
     */
    fun setTo(s: VariableSetting) {
        this.setting = s
    }

    /**
     * Sets the variables state (false,true)
     * Note that if you use watched Literals, then you need to update
     * them in all clauseSets that use this materials.getVariable
     */
    fun setTo(s: Boolean) {
        this.setting = (when (s) {
            true -> VariableSetting.True
            false -> VariableSetting.False
        })
        this.previousSetting = s
    }

    /**
     * Unsets the materials.getVariable (away from true/false)
     * Note that if you use watched Literals, then you need to update
     * them in all clauseSets that use this materials.getVariable
     */
    fun unset() {
        this.setting = VariableSetting.Unset
    }

    val boolSetting: Boolean?
        get() =
            when (this.setting) {
                VariableSetting.True -> true
                VariableSetting.False -> false
                VariableSetting.Unset -> null
            }

    /**
     * if materials.getPredicate is false, then the variables setting is interpreted as negated
     * if the materials.getVariable is not set then false is returned
     */
    fun isTrueWith(predicate: Boolean): Boolean =
            when (this.setting) {
                VariableSetting.Unset -> false
                VariableSetting.True -> predicate
                VariableSetting.False -> !predicate
            }

    fun isFalseWith(predicate: Boolean): Boolean =
            when (this.setting) {
                VariableSetting.Unset -> false
                VariableSetting.True -> !predicate
                VariableSetting.False -> predicate
            }

    val isUnset: Boolean
        get() = this.setting == VariableSetting.Unset

    override fun toString(): String {
        return this.id.toString()
    }

    override fun equals(other: Any?): Boolean {
        if (other is Variable) {
            return this.id.equals(other.id) && this.setting.equals(other.setting)
        } else
            return super.equals(other)
    }

    override fun compareTo(other: Variable): Int
    {
        //an unset var always takes precedence, so that assigned variables are unpreferred
        if (this.isUnset != other.isUnset) {
            return if(this.isUnset) 1 else -1
        }

        return (other.activity - this.activity).let {
            when {
                it > 0 -> -1
                it < 0 -> 1
                else -> 0
            }
        }
    }

}

class VariableSet
{
    private val knownVariables:MutableMap<VariableIdentifier, Variable> = mutableMapOf()

    constructor()

    constructor(vs: VariableSet)
    {
        for (v: Variable in vs.knownVariables.values)
        {
            this.storeOrGet(v.id).setTo(v.setting)
        }
    }

    constructor(vs: Sequence<Variable>)
    {
        vs.forEach { this.knownVariables[it.id] = it}
    }

    fun storeOrGet(id: VariableIdentifier): Variable
    {
        var retu: Variable? = this.knownVariables[id]
        if(retu == null)
        {
            retu = Variable(id)
            this.knownVariables.put(id,retu)
        }
        return retu
    }
}
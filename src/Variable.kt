typealias VariableIdentifier = String
enum class VariableSetting {True,False,Unset}

class Variable constructor(c: VariableIdentifier)
{
    constructor(v: Variable) : this(v.id)
    {
        this.setTo(v.setting)
    }

    var id :VariableIdentifier = c
    init{
        assert(id.isNotBlank())
    }
    var setting : VariableSetting = VariableSetting.Unset

    /**
     * Sets the variables state (false,true,unset)
     * Note that if you use watched Literals, then you need to update
     * them in all clauseSets that use this variable
     */
    fun setTo(s:VariableSetting)
    {
        this.setting = s
    }
    /**
     * Sets the variables state (false,true)
     * Note that if you use watched Literals, then you need to update
     * them in all clauseSets that use this variable
     */
    fun setTo(s: Boolean) {
        this.setting = when (s) {
            true -> VariableSetting.True
            false -> VariableSetting.False
        }
    }

    /**
     * Unsets the variable (away from true/false)
     * Note that if you use watched Literals, then you need to update
     * them in all clauseSets that use this variable
     */
    fun unset() {
        this.setting = VariableSetting.Unset
    }
    val boolSetting :Boolean? get() =
        when(this.setting)
        {
            VariableSetting.True -> true
            VariableSetting.False -> false
            VariableSetting.Unset -> null
        }

    /**
     * if predicate is false, then the variables setting is interpreted as negated
     * if the variable is not set then false is returned
     */
    fun isTrueWith(predicate:Boolean):Boolean =
        when (this.setting) {
            VariableSetting.Unset -> false
            VariableSetting.True -> predicate
            VariableSetting.False -> !predicate
        }
    fun isFalseWith(predicate:Boolean):Boolean =
        when(this.setting){
            VariableSetting.Unset -> false
            VariableSetting.True -> ! predicate
            VariableSetting.False -> predicate
        }
    val isUnset:Boolean
        get() = this.setting == VariableSetting.Unset

    override fun toString():String
    {
        return this.id
    }

    override fun equals(other: Any?): Boolean {
        if (other is Variable) {
            return this.id.equals(other.id) && this.setting.equals(other.setting)
        } else
        return super.equals(other)
    }
}

class VariableSet
{
    private val knownVariables:MutableMap<VariableIdentifier,Variable> = mutableMapOf()

    constructor()

    constructor(vs: VariableSet)
    {
        for (v:Variable in vs.knownVariables.values)
        {
            this.storeOrGet(v.id).setTo(v.setting)
        }
    }

    constructor(vs: Sequence<Variable>)
    {
        vs.forEach { this.knownVariables[it.id] = it}
    }

    fun storeOrGet(id:VariableIdentifier):Variable
    {
        var retu:Variable? = this.knownVariables[id]
        if(retu == null)
        {
            retu = Variable(id)
            this.knownVariables.put(id,retu)
        }
        return retu
    }
}
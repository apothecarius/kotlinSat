typealias VariableIdentifier = String
enum class VariableSetting {True,False,Unset}

class Variable constructor(c: VariableIdentifier)
{
    var id :VariableIdentifier = c
    init{
        assert(id.isNotBlank())
    }
    var setting : VariableSetting = VariableSetting.Unset

    fun setTo(s:VariableSetting)
    {
        this.setting = s
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


    override fun toString():String
    {
        return this.id
    }
}

class VariableSet
{
    private val knownVariables:MutableMap<VariableIdentifier,Variable> = mutableMapOf()

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
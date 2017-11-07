class ClauseWatchedLiterals constructor(disjunction : Array<Literal>):Clause(disjunction)
{
    constructor (c: String,knownVariables:VariableSet) :
            this(codeToLiteralSet(c,knownVariables))
    constructor(cs:Map<Variable,Boolean>) : this(
            cs.map { it -> Pair(it.key,it.value) }.toTypedArray())

    private val initialHead:Int = 0
    private val initialTail:Int = this.literals.size-1

    var watchedHead:Int = initialHead
    var watchedTail:Int = initialTail

    init{

        //crash if no literals given
        assert(watchedTail >= 0)
    }

    fun resetWatchedLiterals():Unit
    {
        // a better way might be feasible, like storing settings in a stack or
        // moving head and tail in a circular fashion
        this.watchedHead = initialHead
        this.watchedTail = initialTail

        while (this.literals[watchedHead].becomesFalse() &&
                this.watchedHead != this.watchedTail &&
                this.watchedHead < this.literals.size) {
            this.watchedHead++
        }
        while (this.literals[watchedTail].becomesFalse() &&
                this.watchedHead != this.watchedTail &&
                this.watchedHead >= 0) {
            this.watchedTail--
        }

    }

    fun updateWatchedLiterals(v: Variable) {
        if (this.isUnit || this.isEmpty || this.isSatisfied) {
            //dont change an established state
            return
        }
        var movingHead:Boolean = when (v) {
            this.literals[watchedHead].variable -> true
            this.literals[watchedTail].variable -> false
            else -> return
        }

        do {
            when (movingHead) {
                true -> this.watchedHead++
                false -> this.watchedTail--
            }
            var wanderingWatched:Literal = this.literals[when (movingHead) {
                true -> watchedHead
                false -> watchedTail
            }]
        } while (this.watchedHead != this.watchedTail &&
                ! wanderingWatched.isUnset &&
                ! this.isSatisfied)
    }


    //benefit of watched literals, the state of the clauses can be
    // determined in O(1)
    override val isUnit:Boolean
            get() = this.watchedHead == this.watchedTail &&
                    this.literals[this.watchedTail].isUnset
    override val isSatisfied: Boolean
        get() = this.literals[watchedHead].becomesTrue() ||
                this.literals[watchedTail].becomesTrue()
    override val isEmpty: Boolean
        get() = this.watchedHead == this.watchedTail &&
                    this.literals[this.watchedTail].becomesFalse()

}
class ClauseWatchedLiterals constructor(disjunction : Array<Literal>):Clause(disjunction)
{
    constructor (c: String,knownVariables:VariableSet) :
            this(codeToLiteralSet(c,knownVariables))
    constructor(cs:Map<Variable,Boolean>) : this(
            cs.map { it -> Pair(it.key,it.value) }.toTypedArray())

    private val initialHead:Int = 0
    private val initialTail:Int = this.literals.size-1

    var watchedHead:Int = initialHead
    set(value){
        field = value
        if (field >= this.literals.size) {
            field = field % this.literals.size
        }
        while (field < 0) { //modulo doesnt work correctly in java/kotlin
            field += this.literals.size
        }
    }
    var watchedTail:Int = initialTail
    set(value){
        field = value
        if (field >= this.literals.size) {
            field = field % this.literals.size
        }
        while (field < 0) {
            field += this.literals.size
        }
    }

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

        this.updateWatchedLiterals(this.literals[this.watchedHead].variable)
        this.updateWatchedLiterals(this.literals[this.watchedTail].variable)
    }


    fun updateWatchedLiterals(v: Variable) {
        if (this.isUnit || this.isEmpty || this.isSatisfied) {
            //dont change an established state
            return
        } else if (v.isUnset) {
            //dont need to move away from an unset variable
            return
        }

        val isMovingHead: Boolean = when (v) {
            this.literals[watchedHead].variable -> true
            this.literals[watchedTail].variable -> false
            else -> return
        }

        //would be nice to have this as dynamic variable
        fun getMovingLiteral() = this.literals[when (isMovingHead) {
            true -> watchedHead
            false ->watchedTail
        }]



        val initialWanderingLiteral = getMovingLiteral()


        fun mustKeepMovingWatchedLiteral(wanderingWatched: Literal): Boolean {
            return when (activeWLIterationScheme) {
                WatchedLiteralIterationScheme.ToMiddle ->
                    this.watchedHead != this.watchedTail &&
                    !wanderingWatched.isUnset &&
                    !this.isSatisfied
                WatchedLiteralIterationScheme.SideBySide ->
                    !wanderingWatched.becomesTrue() &&
                    wanderingWatched != initialWanderingLiteral &&
                    ! (wanderingWatched.isUnset && this.watchedHead != this.watchedTail)
            }
        }

        fun moveActiveWatchedLiteral() = when (isMovingHead) {
            true -> this.watchedHead++
            false -> when (activeWLIterationScheme) {
                WatchedLiteralIterationScheme.ToMiddle -> this.watchedTail--
                WatchedLiteralIterationScheme.SideBySide -> this.watchedTail++
            }
        }

        do {
            moveActiveWatchedLiteral()
        } while (mustKeepMovingWatchedLiteral(getMovingLiteral()))

        //if a full rotation happened a unit case is recognized when both
        //watched literals are at the same position
        if (activeWLIterationScheme == WatchedLiteralIterationScheme.SideBySide) {
            if(initialWanderingLiteral == getMovingLiteral())
            {
                if (isMovingHead) {
                    this.watchedHead = this.watchedTail
                } else {
                    this.watchedTail = this.watchedHead
                }
            }
        }

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
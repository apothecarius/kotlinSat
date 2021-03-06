package materials

import support.assert


enum class WatchedLiteralIterationScheme {
    ToMiddle, SideBySide
}

class ClauseWatchedLiterals constructor(disjunction: Array<Literal>) : Clause(disjunction) {
    constructor (c: String, knownVariables: VariableSet) :
            this(codeToLiteralSet(c, knownVariables))

    constructor(c: ClauseWatchedLiterals, vs: VariableSet) : this(c.literals.map { it: Literal -> Literal(vs.storeOrGet(it.variable.id),it.predicate) }.toTypedArray())
    //constructor(c: materials.Clause) : this(c.literals.map { it:materials.Literal -> materials.Literal(materials.Variable(it.materials.getVariable),it.materials.getPredicate) }.toTypedArray())
    constructor(l: Literal) : this(arrayOf(l))
    constructor(cs: Map<Variable, Boolean>) : this(
            cs.map { it -> Pair(it.key, it.value) }.toTypedArray())


    private val initialHead: Int = 0
    private val initialTail: Int
        get() = this.literals.size - 1

    companion object {
        /**
         * This flag changes the use of the watched literals for the purpose
         * of finding the primeImplicant of the associated clauseSet.
         * If set to false the watchedLiterals will stay on literals that fulfill
         * the clause, if true on unset literals
         * TODO be explicit and use an enum
         */
        var watchedLiteralsForUnitVariables: Boolean = true

        /**
         * Watched literals march over the clauses literals and there are two established schemes how this can be done
         * Either both pointers start at either end of the clause and march towards the middle until they meet
         * Or they start next to each other both moving forward.
         */

        val activeWLIterationScheme:WatchedLiteralIterationScheme = WatchedLiteralIterationScheme.ToMiddle
    }

    var watchedHead: Int = initialHead
        set(value) {
            field = value
            if (field >= this.literals.size) {
                field = field % this.literals.size
            }
            while (field < 0) { //modulo doesnt work correctly in java/kotlin
                field += this.literals.size
            }
        }
    var watchedTail: Int = initialTail
        set(value) {
            field = value
            if (field >= this.literals.size) {
                field = field % this.literals.size
            }
            while (field < 0) {
                field += this.literals.size
            }
        }

    init {

        //crash if no literals given
        assert { watchedTail >= 0 }
    }

    fun resetWatchedLiterals() {
        // a better way might be feasible, like storing settings in a stack or
        // moving head and tail in a circular fashion
        this.watchedHead = initialHead
        this.watchedTail = initialTail


        this.updateWatchedLiterals(this.literals[this.watchedHead].variable)
        this.updateWatchedLiterals(this.literals[this.watchedTail].variable)

        if (activeWLIterationScheme == WatchedLiteralIterationScheme.ToMiddle) {
            assert { this.watchedHead <= this.watchedTail }
        }
    }

    /**
     * This function checks whether the passed variables is one of the two
     * watched literals and in that case moves that index to another unwatched
     * literal
     *
     * If the clauses are set to find a primeImplicant the function seeks a
     * fulfilled literal
     */
    fun updateWatchedLiterals(v: Variable) {
        if (watchedLiteralsForUnitVariables) {
            if (this.isUnit || this.isEmpty || this.isSatisfied) {
                //dont change an established state
                return
            } else if (v.isUnset) {
                //dont need to move away from an unset materials.getVariable
                return
            }
        }

        val isMovingHead: Boolean = when (v) {
            this.literals[watchedHead].variable -> true
            this.literals[watchedTail].variable -> false
            else -> return
        }

        //would be nice to have this as dynamic materials.getVariable
        fun getMovingLiteral(): Literal = this.literals[when (isMovingHead) {
            true -> watchedHead
            false -> watchedTail
        }]
        val initialWanderingLiteral = getMovingLiteral()
        if (!watchedLiteralsForUnitVariables) {
            if (initialWanderingLiteral.becomesTrue()) {
                return
            }
        }



        fun mustKeepMovingWatchedLiteral(wanderingWatched: Literal): Boolean {
            if (watchedLiteralsForUnitVariables) {
                return when (activeWLIterationScheme) {
                    WatchedLiteralIterationScheme.ToMiddle ->
                        this.watchedHead != this.watchedTail &&
                                !wanderingWatched.isUnset &&
                                !this.isSatisfied
                    WatchedLiteralIterationScheme.SideBySide ->
                        !wanderingWatched.becomesTrue() &&
                                wanderingWatched != initialWanderingLiteral &&
                                !(wanderingWatched.isUnset && this.watchedHead != this.watchedTail)
                }
            } else {
                assert { activeWLIterationScheme == WatchedLiteralIterationScheme.ToMiddle }
                return when (activeWLIterationScheme) {
                    WatchedLiteralIterationScheme.ToMiddle ->
                        this.watchedHead != this.watchedTail &&
                                !wanderingWatched.becomesTrue()
                    WatchedLiteralIterationScheme.SideBySide ->
                        true //TODO implement and test
                }
            }
        }

        fun moveActiveWatchedLiteral() = when (isMovingHead) {
            true -> this.watchedHead++
            false -> when (activeWLIterationScheme) {
                WatchedLiteralIterationScheme.ToMiddle -> this.watchedTail--
                WatchedLiteralIterationScheme.SideBySide -> this.watchedTail++
            }
        }

        //the central loop of what this function does
        do {
            moveActiveWatchedLiteral()
        } while (mustKeepMovingWatchedLiteral(getMovingLiteral()))

        //if a full rotation happened a unit case is recognized when both
        //watched literals are at the same position
        if (activeWLIterationScheme == WatchedLiteralIterationScheme.SideBySide) {
            if (initialWanderingLiteral == getMovingLiteral()) {
                if (isMovingHead) {
                    this.watchedHead = this.watchedTail
                } else {
                    this.watchedTail = this.watchedHead
                }
            }
        }

    }

    /**
     * returns true, if only one literal fulfills this clause
     */
    fun isPrimeFulfilled(): Boolean {
        return this.getPrimeLiteral() != null
    }

    /**
     * returns the unique literal that fulfills this clause, or null if
     * multiple candidates with this condition exist
     */
    fun getPrimeLiteral(): Literal? {
        assert { !watchedLiteralsForUnitVariables }
        return if (this.watchedHead == this.watchedTail) {
            this.literals[this.watchedTail]
        } else {
            null
        }
    }


    //benefit of watched literals, the state of the clauses can be
    // determined in O(1)
    override val isUnit: Boolean
        get() {
            return this.watchedHead == this.watchedTail &&
                    this.literals[this.watchedTail].isUnset
        }
    override val isSatisfied: Boolean
        get() {
            //assert{watchedLiteralsForUnitVariables}
            return this.literals[watchedHead].becomesTrue() ||
                    this.literals[watchedTail].becomesTrue()
        }
    override val isEmpty: Boolean
        get() {
            //assert{watchedLiteralsForUnitVariables}
            return this.watchedHead == this.watchedTail &&
                    this.literals[this.watchedTail].becomesFalse()
        }


    fun getBothWatchedLiterals(): Pair<Literal, Literal?> {
        return Pair(this.literals[this.watchedHead],
                if (this.watchedHead != this.watchedTail) {
                    this.literals[this.watchedTail]
                } else {
                    null
                })
    }

    override fun filterFalsyLiterals() {
        super.filterFalsyLiterals()
        this.resetWatchedLiterals()
    }
}



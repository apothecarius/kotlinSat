open class LiteralOccurenceNode constructor(myLit:Literal){
    val myLiteral:Literal = myLit
    var storedClause:ClauseWatchedLiterals? = null
    val children:MutableMap<Literal,LiteralOccurenceNode> = mutableMapOf()


    fun storeClause(toStore: ClauseWatchedLiterals, litIdx:Int,myFln:FirstLiteralNode,
                    inTree:SubsumptionTree):List<ClauseWatchedLiterals> {
        assert(this.myLiteral == toStore.literals[litIdx])

        if (litIdx + 1 == toStore.literals.count()) {
            //reached end of toStore
            if (this.storedClause != null) {
                //found a duplicate of the clause
                assert(this.storedClause == toStore)
                return listOf(toStore)
            }
            //put it right here
            this.storedClause = toStore
            val retu:List<ClauseWatchedLiterals> = this.children.values.
                    flatMap { it.clearChildren() }
            this.children.clear()
            return retu
        }
        else if (this.storedClause != null) {
            return listOf(toStore)
            //still literals in toStore, but I followed literals of an already stored clause,
            // implying that toStore gets subsumed
        }

        //else go down the graph
        val nextLiteral:Literal = toStore.literals[litIdx + 1]
        //literals are assumed to be sorted
        assert(nextLiteral.variable.id > toStore.literals[litIdx].variable.id)

        if (this.children[nextLiteral] == null) {
            //need to make the next node
            val nuNode = LiteralOccurenceNode(nextLiteral)
            this.children[nextLiteral] = nuNode
            if(inTree[nextLiteral] != null)
            {
                //need to refer this new node, to its FLN
                val itsFLN = inTree[nextLiteral]!!

                itsFLN.extraLiteralOccurenceNodes.add(Pair(myFln,nuNode))
            }
        }
        return this.children[nextLiteral]!!.storeClause(toStore,litIdx+1,myFln,inTree)
    }


    /**
     * Should remove all children of this node and return the contained clauses
     */
    private fun clearChildren(): List<ClauseWatchedLiterals> {
        val retu:List<ClauseWatchedLiterals>

        if (this.storedClause != null) {
            assert(this.children.isEmpty())//they would all be subsumed
            retu = listOf(this.storedClause!!)
            this.storedClause = null

        } else {
            retu = this.children.values.flatMap { it.clearChildren() }
            this.children.clear()
        }
        return retu
    }
}

class FirstLiteralNode constructor(myLit:Literal): LiteralOccurenceNode(myLit){

    val extraLiteralOccurenceNodes:MutableList<Pair<FirstLiteralNode,LiteralOccurenceNode>> =
            mutableListOf()

    fun storeClause(toStore: ClauseWatchedLiterals, litIdx:Int,
                             inTree:SubsumptionTree):List<ClauseWatchedLiterals> {
        assert(this.myLiteral == toStore.literals[litIdx])


        return super.storeClause(toStore, litIdx,this, inTree)// + forach(this.extraLiteralOccurenceNodes -> storeclause)
    }

    open val extraLonNotation:String get(){
        var retu = this.extraLiteralOccurenceNodes.map {
            it.first.myLiteral.toString()+".."+it.second.myLiteral }

        return if(retu.isEmpty()) "" else "[${retu.joinToString(",")}]"
    }


}

typealias SubsumptionTree = MutableMap<Literal,FirstLiteralNode>

/**
 * stores the given clause in this graph, returns the subsumed clauses,
 * which should then be removed from the clauseset.
 */
fun SubsumptionTree.storeClause(toStore: ClauseWatchedLiterals):
        Either<List<ClauseWatchedLiterals>,String>
{
    val firstLit = toStore.literals[0]
    var itsFLN:FirstLiteralNode? = this[firstLit]
    if (itsFLN == null) {
        itsFLN = FirstLiteralNode(firstLit)
        this[firstLit] = itsFLN
    }

    val retu = itsFLN.storeClause(toStore,0,this)

    //input was rejected, because it was already subsumpted
    if (retu.count() == 1 && retu[0] === toStore) {
        return Either.Right("Rejected")
    }
    return Either.Left(retu)
}

fun SubsumptionTree.print(){

    fun printLON(lon: LiteralOccurenceNode, depth: Int) {
        val clauseToWrite:String = if(lon.storedClause != null)
            " -> "+lon.storedClause.toString()
        else ""

        val mid:String =lon.myLiteral.writeShort + clauseToWrite

        val line:String = if (lon is FirstLiteralNode) {
            ":" + mid + lon.extraLonNotation
        } else {
            " " + "  ".repeat(depth) + mid
        }

        println(line)
        for (subNode in lon.children.values) {
            printLON(subNode,depth+1)
        }
    }

    for (fln in this.values){
        printLON(fln,0)

    }

}
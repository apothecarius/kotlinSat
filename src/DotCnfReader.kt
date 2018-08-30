import java.io.File
import kotlin.math.absoluteValue
import kotlin.math.sign
import kotlin.test.assert

fun readCnf(file:File) : ClauseSetWatchedLiterals
{
    val reader = file.bufferedReader();

    val clauses = listOf<ClauseWatchedLiterals>()

    var isSpecified:Boolean = false
    val knownVars:VariableSet = VariableSet()
    val clauseList:MutableList<ClauseWatchedLiterals> = emptyList<ClauseWatchedLiterals>().toMutableList()
    for (line: String in reader.lines())
    {
        if (line.startsWith("c")) {
            continue
        }
        else if (line.startsWith("p"))
        {
            val splits = line.split(" ")
            assert(splits[1] == "cnf")
            val numVars = splits[2].toInt()
            assert(numVars > 0)
            val numClauses = splits[3].toInt()
            assert(numClauses > 0)
            isSpecified = true

            var i:Int = 1
            while (i <= numVars) {
                knownVars.storeOrGet(i.toString())
                i++
            }

        }
        else
        {
            assert(isSpecified)
            val splits = line.split(" ")
            assert(splits.count() >= 2)
            assert(splits[splits.count()-1] == "0")

            val disj:Array<Literal> = splits.subList(0,splits.count()-1).
                    map { it -> it.toInt() }.
                    map {it:Int -> Literal(knownVars.storeOrGet(it.absoluteValue.toString()),it > 0)
            }.toTypedArray()

            val nuClause:ClauseWatchedLiterals = ClauseWatchedLiterals(disj)
            clauseList.add(nuClause)
        }
    }

    return ClauseSetWatchedLiterals(clauseList.toTypedArray())
}
package support

object Helpers {


    /**
     * Converts a char from 0 to 9 to a number
     * Throws an exception on any other input
     */
    fun digitToInt(c:Char):Int
    {
        var asInt:Int = c.toInt()-48

        if(asInt < 0 || asInt > 9) throw Exception("Called Helpers.digitToInt with nondecimal single-digit value")
        return asInt
    }
}
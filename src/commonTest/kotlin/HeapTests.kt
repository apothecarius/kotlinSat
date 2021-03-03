import support.Heap
import materials.Variable
import kotlin.random.Random
import kotlin.test.*

class HeapTests{
    @Test
    fun sizeTest()
    {
        val h: Heap<Int> = Heap()
        assertEquals(0,h.size())
        h.add(5)
        assertEquals(1,h.size())
        h.add(1)
        assertEquals(2,h.size())
        h.pop()
        assertEquals(1,h.size())
        h.pop()
        assertEquals(0,h.size())
    }


    @Test
    fun insertionOrderTest()
    {
        val h: Heap<Int> = Heap()
        assertEquals(null,h.pop())

        h.add(1)
        h.add(5)
        h.add(3)
        assertEquals(5,h.pop())
        assertEquals(3,h.pop())
        assertEquals(1,h.pop())
        assertEquals(null,h.pop())
    }

    @Test
    fun largeInsertionOrderTest()
    {
        val h = Heap<Int>()
        for (i in 1..100) {
            val v = Random.nextInt() % 200
            h.add(v)
        }

        assertTrue(verifyMonotonicity(h))
    }

    @Test
    fun largeInsertionOrderVariableTest()
    {
        val h = Heap<Variable>()
        for (i in 1..1000) {
            val v = Variable(i.toString())
            v.activity = Random.nextFloat()*10000f
            h.add(v)
        }

        assertTrue(verifyMonotonicity(h))
    }

    @Test
    fun largeInsertionOrderVariableTestWithChanges()
    {
        val h = Heap<Variable>()
        val vars:MutableList<Variable> = mutableListOf()
        for (i in 1..1000) {
            val v = Variable(i.toString())
            v.activity = Random.nextFloat()*10000f
            vars.add(v)
            h.add(v)
        }
        assertTrue(verifyMonotonicity(h))
        for (v in vars) {
            v.activity = Random.nextFloat()*10000f
        }
        h.reorder()

        assertTrue(verifyMonotonicity(h))
    }

    private fun<T : Comparable<T>> verifyMonotonicity(h: Heap<T>):Boolean
    {
        var previous:T? = null
        while (h.size() != 0)
        {
            val current = h.pop()!!
            if (previous == null) {
                previous = current
                continue
            }
            if(current > previous)
                return false
            previous = current
        }
        return true
    }

    @Test
    fun reorderTest()
    {
        val vara = Variable("a")
        vara.activity = 1f
        val varb = Variable("b")
        varb.activity = 2f
        val varc = Variable("c")
        varc.activity = 3f
        val vard = Variable("d")
        vard.activity = 4f

        val h: Heap<Variable> = Heap()
        h.add(vara)
        h.add(varb)
        h.add(varc)
        h.add(vard)

        vara.activity = 4f
        varb.activity = 3f
        varc.activity = 2f
        vard.activity = 1f

        h.reorder()

        assertEquals(vara,h.pop())
        assertEquals(varb,h.pop())
        assertEquals(varc,h.pop())
        assertEquals(vard,h.pop())
        assertEquals(null,h.pop())
    }


    @Test
    fun unassignedVariablesComeFirstTest()
    {
        val h: Heap<Variable> = Heap()
        var hasAssi:Boolean = true
        for (i in 1..1000) {
            val v = Variable(i.toString())
            v.activity = Random.nextFloat()*10000f
            if (hasAssi) {
                v.setTo(true)
            }
            hasAssi = !hasAssi
            h.add(v)
        }

        h.reorder()

        //variables without assignment should come out first,
        // then those with assignment
        hasAssi = false
        while (!h.isEmpty()) {
            val cur = h.pop()!!
            if (!hasAssi && !cur.isUnset) {
                hasAssi = true
            } else if(hasAssi) //cant go back
            {
                assertFalse(cur.isUnset)
            }
        }
    }

}
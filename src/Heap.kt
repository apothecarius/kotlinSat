import org.junit.Test
import java.util.*
import kotlin.math.max
import kotlin.math.min
import kotlin.test.*

class Heap<T : Comparable<T>>()
{
    constructor(elements:Sequence<T>) : this()
    {
        elements.forEach { this.add(it)}
    }

    class BinaryTree<T: Comparable<T>>(parParam:BinaryTree<T>?, contentParam:T?)
    {
        private var content:T? = contentParam
        private var left:BinaryTree<T>? = null
        private var right:BinaryTree<T>? = null
        private var parent:BinaryTree<T>? = parParam

        fun size():Int = (if(this.content != null) 1 else 0) +
                (this.left?.size() ?: 0) +
                (this.right?.size() ?: 0)
        fun isEmpty():Boolean = this.size() == 0
        private fun depth():Int = 1 + max((this.left?.depth() ?: 0) , (this.right?.depth() ?: 0))
        private fun minDepth():Int = 1 + min((this.left?.minDepth() ?: 0) , (this.right?.minDepth() ?: 0))

        fun add(e:T)
        {
            //try to insert the element leftmost
            if (this.content == null) {
                this.content = e
                return
            }
            if (this.left == null) {
                this.left = BinaryTree(this,e)
                this.left!!.rebalanceUp()
            } else if (this.right == null) {
                this.right = BinaryTree(this,e)
                this.right!!.rebalanceUp()
            }
            else{
                val leftMinDepth = this.left!!.minDepth()
                val rightMinDepth = this.right!!.minDepth()
                assert(rightMinDepth <= leftMinDepth)
                if(leftMinDepth <= rightMinDepth)
                {
                    this.left!!.add(e)
                    this.left!!.rebalanceUp()
                }

                else if (leftMinDepth > rightMinDepth)
                {
                    this.right!!.add(e)
                    this.right!!.rebalanceUp()
                }
            }
        }

        private fun popLowest():T?
        {
            val leftDepth = this.left?.depth() ?: 0
            val rightDepth = this.right?.depth() ?: 0
            if (leftDepth == 0 && rightDepth == 0) {
                //return this
                val retu = this.content
                this.content = null
                return retu
            } else if (rightDepth == leftDepth) {
                val retu = this.right!!.popLowest()
                if (this.right!!.isEmpty()) {
                    this.right = null
                }
                return retu
            } else
            {
                val retu = this.left!!.popLowest()
                if (this.left!!.isEmpty()) {
                    this.left = null
                }
                return retu
            }
        }
        fun pop():T?
        {
            val replacement:T? = this.popLowest()
            return if (this.content == null) {
                replacement
            }else{
                val retu:T = this.content!!
                this.content = replacement
                this.rebalanceDown()
                retu
            }
        }

        private fun rebalanceDown()
        {
            assert(this.content != null)
            if (this.left == null && this.right == null) {
                return
            }
            else if(this.right == null || this.right!!.content!! < this.left!!.content!!)
            {
                if(this.content!! < this.left!!.content!!)
                {
                    val swap = this.content!!
                    this.content = this.left!!.content
                    this.left!!.content = swap
                    this.left!!.rebalanceDown()
                }
            }
            else
            {
                if(this.content!! < this.right!!.content!!)
                {
                    val swap = this.content!!
                    this.content = this.right!!.content
                    this.right!!.content = swap
                    this.right!!.rebalanceDown()
                }
            }
        }


        private fun rebalanceUp()
        {
            if (this.parent == null) {
                return
            }
            if(this.content!! > this.parent!!.content!!)
            {
                val swap = this.content
                this.content = this.parent!!.content
                this.parent!!.content = swap
                this.parent!!.rebalanceUp()
            }
        }

        fun reorder() {
            if (this.content == null) {
                return
            }
            if(this.left == null && this.right == null)
            {
                this.rebalanceUp()
            }
            else{
                this.left?.reorder()
                this.right?.reorder()
            }

        }
    }

    fun reorder()
    {
        //TODO take the element that changed as parameter, search for it and rebalance from there
        // (probably up and down should be enough)
        if(this.tree != null)
        {
            this.tree!!.reorder();
        }

    }

    private var tree:BinaryTree<T>? = null

    fun size():Int =
        if(this.tree != null)
            this.tree!!.size()
        else 0
    fun isEmpty():Boolean = this.size() == 0

    fun add(e:T)
    {
        if (this.tree == null) {
            this.tree = BinaryTree(null,e)
        } else {
            this.tree!!.add(e)
        }
    }

    fun pop(): T? =
        if (tree == null)
        {
            null
        }else
        {
            tree!!.pop()
        }
}


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
        val randy = Random()
        for (i in 1..100) {
            val v = randy.nextInt() % 200
            h.add(v)
        }

        assertTrue(verifyMonotonicity(h))
    }

    @Test
    fun largeInsertionOrderVariableTest()
    {
        val h = Heap<Variable>()
        val randy = Random()
        for (i in 1..1000) {
            val v = Variable(i.toString())
            v.activity = randy.nextFloat()*10000f
            h.add(v)
        }

        assertTrue(verifyMonotonicity(h))
    }

    @Test
    fun largeInsertionOrderVariableTestWithChanges()
    {
        val h = Heap<Variable>()
        val randy = Random()
        val vars:MutableList<Variable> = LinkedList()
        for (i in 1..1000) {
            val v = Variable(i.toString())
            v.activity = randy.nextFloat()*10000f
            vars.add(v)
            h.add(v)
        }
        assertTrue(verifyMonotonicity(h))
        for (v in vars) {
            v.activity = randy.nextFloat()*10000f
        }
        h.reorder()

        assertTrue(verifyMonotonicity(h))
    }

    private fun<T : Comparable<T>> verifyMonotonicity(h:Heap<T>):Boolean
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

        val h:Heap<Variable> = Heap()
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
        val h:Heap<Variable> = Heap()
        val randy = Random()
        var hasAssi:Boolean = true
        for (i in 1..1000) {
            val v = Variable(i.toString())
            v.activity = randy.nextFloat()*10000f
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
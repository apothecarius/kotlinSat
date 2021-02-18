import org.junit.Test
import java.util.*
import kotlin.math.max
import kotlin.math.min
import kotlin.test.*

class Heap<T : Comparable<T>>
{
    class BinaryTree<T: Comparable<T>>(parParam:BinaryTree<T>?, contentParam:T?)
    {
        var content:T? = contentParam
        var left:BinaryTree<T>? = null
        var right:BinaryTree<T>? = null
        var parent:BinaryTree<T>? = parParam

        fun size():Int = (if(this.content != null) 1 else 0) +
                (this.left?.size() ?: 0) +
                (this.right?.size() ?: 0)
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
                if (this.right!!.size() == 0) {
                    this.right = null
                }
                return retu
            } else
            {
                val retu = this.left!!.popLowest()
                if (this.left!!.size() == 0) {
                    this.left = null
                }
                return retu
            }
        }
        fun pop():T?
        {
            val replacement:T? = this.popLowest()
            if (this.content == null) {
                return replacement
            }else{
                val retu:T = this.content!!
                this.content = replacement
                this.rebalanceDown()
                return retu
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
    }


    private var tree:BinaryTree<T>? = null

    fun size():Int =
        if(this.tree != null)
            this.tree!!.size()
        else 0

    fun add(e:T):Unit
    {
        if (this.tree == null) {
            this.tree = BinaryTree<T>(null,e)
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

        //expected that activity monotonically rises
        var prevActivity: Int = Int.MAX_VALUE
        while (h.size() != 0)
        {
            val v = h.pop()!!
            val curActivity = v
            assertTrue(curActivity <= prevActivity)
            prevActivity = curActivity
        }

    }

    @Test
    fun largeInsertionOrderVariableTest()
    {
        val h = Heap<Variable>()
        val randy = Random()
        for (i in 1..100) {
            val v = Variable(i.toString())
            v.activity = randy.nextFloat()*10000f
            h.add(v)
        }

        //expected that activity monotonically rises
        var prevActivity: Float = Float.MAX_VALUE
        while (h.size() != 0)
        {
            val v = h.pop()!!
            val curActivity = v.activity
            assertTrue(curActivity <= prevActivity)
            prevActivity = curActivity
        }

    }
}
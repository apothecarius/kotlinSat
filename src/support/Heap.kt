package support

import kotlin.math.max
import kotlin.math.min

class Heap<T : Comparable<T>>()
{
    constructor(elements:Sequence<T>) : this()
    {
        elements.forEach { this.add(it)}
    }

    class BinaryTree<T: Comparable<T>>(parParam: BinaryTree<T>?, contentParam:T?)
    {
        private var content:T? = contentParam
        private var left: BinaryTree<T>? = null
        private var right: BinaryTree<T>? = null
        private var parent: BinaryTree<T>? = parParam

        fun size():Int = (if(this.content != null) 1 else 0) +
                (this.left?.size() ?: 0) +
                (this.right?.size() ?: 0)
        fun isEmpty():Boolean = this.size() == 0
        private fun depth():Int = 1 + max((this.left?.depth() ?: 0) , (this.right?.depth() ?: 0))
        private fun minDepth():Int = 1 + min((this.left?.minDepth() ?: 0) , (this.right?.minDepth() ?: 0))

        fun _getAllContent():List<T> = listOf(this.content!!) +
            (this.left?._getAllContent()?: emptyList<T>()) +
            (this.right?._getAllContent()?: emptyList<T>())


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

    private var tree: BinaryTree<T>? = null

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



package support

sealed class Either<out A, out B> {
    class Left<A>(val value: A): Either<A, Nothing>()
    class Right<B>(val value: B): Either<Nothing, B>()

    override fun toString(): String {
        return when (this) {
            is Left -> {
                this.value.toString()
            }
            is Right -> {
                this.value.toString()
            }
        }
    }
}
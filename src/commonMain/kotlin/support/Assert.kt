package support

//TODO check -ea flag or something
private const val assertionsAreOn:Boolean = true

fun assert(assertionBlock:(()->Boolean), err:String = "")
{
    if(assertionsAreOn)
    {
        if(!assertionBlock())
        {
            throw Error(err)
        }
    }
}

fun assert(assertionBlock:(()->Boolean))
{
    assert(assertionBlock,"")
}
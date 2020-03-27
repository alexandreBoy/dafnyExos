method Carre(a: nat) returns (c: int)
{
    var i := 0;
    c := 0;
    while i != a
        invariant i <= a
        decreases a-i
    {
        c := c + 2*i + 1;
        i := i + 1;
    }
}
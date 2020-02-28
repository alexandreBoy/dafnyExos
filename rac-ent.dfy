method rac(n:nat) returns (r:nat)
{
    var c:int := 0;
    var s:int := 1;
    while s <= n
        decreases n-s
        invariant c >= 0
    {
        c := c + 1;
        s := s + 2*c +1;
    }
}
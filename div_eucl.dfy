method div_eucl(a:nat, b:nat) returns (q:nat, r:nat)
requires b > 0
ensures a == b*q+r && 0 <= r < b
{
    r := a;
    q := 0;
    while b <= r
        decreases r-b
        invariant a == b*q + r
    {
        r := r-b;
        q := q+1;
    }
}
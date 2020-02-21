// Exercice 20 du cours sur la terminaison

method pgcd(a:int, b:int) returns (p:int)
    requires a > 0 && b > 0
    // pas de post-conditions
    {
        var u:int := a;
        var v:int := b;
        while u != v 
            invariant u > 0 && v > 0
            decreases u + v
        {
            if u > v { u := u - v; }
            else { v := v - u; }
        }
        p := u;
        return p;
    }
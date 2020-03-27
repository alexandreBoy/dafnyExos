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

// Correction totale = Correction partielle + terminaison
// Termininaison pour Carre : exo 3 du partiel
// Correction partielle :
// En (3) je sais : inv (les 2) + non(i!=a)
// i <= a && c = i*i && i = a
// => c = a*a

method Carre2(a: int) returns (c: int)
requires a >= 0
ensures c == a*a
{
    var i := 0;
    c := 0;
    while i != a
        invariant i <= a
        invariant c == i*i
        decreases a-i
    {
        c := c + 2*i + 1;
        i := i + 1;
    }
    // (3) c == a*a
    return c;
}
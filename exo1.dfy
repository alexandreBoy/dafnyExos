// Exercice 1

method sumMax(x: int, y: int) returns (s: int, m: int) // s : la somme et m : le maximum
    ensures s == x + y
    ensures x <= m && y <= m
    ensures m == x || m == y // m est l'un des deux
{
    s := x + y;
    if x < y
    {
        m := y;
    }
    else
    {
        m := x;
    }
}
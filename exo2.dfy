// Exercice 2

method SumMaxBackwards(s: int, m: int) returns (x: int, y: int)
    ensures s == x + y
    ensures x <= m && y <= m
    ensures m == x || m == y // m est l'un des deux
    // écrire l'implémentation de summax en backwards : utiliser une pré condition qui est la plus large possible
    requires 2*m >= s
{
    x := s - m;
    y := m;
}

method SumMaxBackwards2(s: int, m: int) returns (x: int, y: int)
    ensures s == x + y
    ensures x <= m && y <= m
    ensures m == x || m == y // m est l'un des deux
    // écrire l'implémentation de summax en backwards : utiliser une pré condition qui est la plus large possible
    requires 2*m >= s
{
    x := m;
    y := s - x;
}
// Exercice 3

method CountToAndReturnN(n: int) returns (r: int)
    requires n >= 0
    ensures r == n 
{
    var i := 0;
    while i < n
      invariant i <= n
    {
        i := i + 1;
    }
    r := i;
}

/*
    Invariant de boucle :
        à chaque fois que l'exécution passe sur (*), i <= n

    Méthode pour justifier les invariants inductifs
    Cas de base : la 1ère fois, la formule est vraie
    Cas inductif : je suppose formule OK en (*) 

*/
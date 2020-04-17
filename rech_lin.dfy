method rech_lin(L:array<int>, a:int) returns (res:bool)
requires L.Length >= 1;
ensures res ==> exists 1 :: 0 <= i < L.Length && L[i] == a
ensures !res ==> forall i :: 0 <= i < L.Length ==> L[i] != a
{
    var i:int := 0;
    // (*)
    while i < L.Length && L[i] != a
        invariant 0 <= i <= L.Length
        invariant forall j :: 0 <= j < i ==> L[j] != a // on a pas vu a donc on continu d'avancer
        decreases L.Length-i
    {
            i := i + 1;
    }
    // (F) : [forall j :: 0 <= j < i ==> L[j] != a] && non(i < L.Length && L[i] != a)
    // => post-condition
    res := (i < L.Length);
}
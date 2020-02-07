method LinearSearch(a:array<int>, key:int) returns (r:int)
  ensures 0 <= r ==> r < a.Length && a[r]==key
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
{
  var i := 0;
    while i < a.Length
    decreases a.Length-i
    invariant 0 <= i <= a.Length
    invariant forall j :: 0 <= j < i ==> a[j] != key
    {
      if a[i] == key
      {
        return i;
      }
      i := i+1;
    } 
    return -1; // commentaire pour tester git
}
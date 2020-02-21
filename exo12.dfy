method LinearSearch(a:array<int>, key:int) returns (r:int)
  ensures 0 <= r ==> r < a.Length && a[r]==key
  ensures r < 0 ==> forall i :: 0 <= i < a.Length ==> a[i] != key
{
    var j:int := 0;
    while j < a.Length 
        decreases a.Length - j
        invariant 0 <= j <= a.Length
        invariant forall k :: 0 <= k < j ==> a[k] != key
    
    {
        if a[j] == key {return j;}
        j := j + 1;

    }
    return -2020;
}
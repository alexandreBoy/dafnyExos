method Sum(a: nat, b: nat) returns (s: nat)
//ensures s == a+b
{
  var x:int := a;
  var y:int := b;
  while y != 0
        invariant y >= 0 && x >= 0
        decreases y
  {
    x := x+1;
    y := y-1;
  }
  s := x;
}
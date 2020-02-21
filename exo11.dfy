method Sum(a: nat, b: nat) returns (s: nat)
ensures s == a+b
{
  var x, y := a, b;
  while y != 0
        ...
  {
    x := x+1;
    y := y-1;
  }
  s := x;
}
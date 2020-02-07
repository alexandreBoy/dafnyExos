function Fibonacci(n: nat): nat
decreases n
{
  if n < 2 then n else Fibonacci(n-2) + Fibonacci(n-1)
}

method ComputeFib(n :nat) returns (x: nat)
    ensures x == Fibonacci(n)
    {
        x := 0;
        var y := 1;
        var i := 0;
            while i < n
                invariant 0 <= i <= n
                invariant x == Fibonacci(i) && y == Fibonacci(i+1)
                {
                    x, y := y, x + y; // Fibonacci(i+2) = Fibonacci(i) + Fibonacci(i+1)
                    i := i+1;
                }
    }
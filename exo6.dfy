function Sum(n: nat): nat
    {
        if n == 0 then 0 else n + Sum(n-1)
    }

method ComputeSum(n: nat) returns (s: nat)
    ensures s == Sum(n)
    // écrire avec une boucle
    {
        var i := 0;
        s := 0;

            while i < n
                invariant 0 <= i <= n
                invariant s == Sum(i)
                decreases n-i
                {
                    i := i + 1;
                    s := s + i;

                }
                0 <= i <= n && i >= n && s == Sum(i)

    }
function exp(a:nat, n:nat): nat
decreases n
{
    if n==0 then 1 else a * exp(a,n-1)
}

method apn_lineaire(a:nat, n:nat) returns (R:nat)
ensures R==exp(a,n)
{
    var A:nat := a;
    var N:nat := n;
    R := 1;
    // (*)
    while N > 0
        invariant exp(A,N)*R == exp(a,n)
        decreases N
    {
        R := R*A;
        N := N-1;
    }
    // (F) : exp(A,N)*R == exp(a,n) + non(N > 0) => N=0 && 1*R = exp(a,n)
}

method apn_log0(a:nat, n:nat) returns (R:nat)
//ensures R==exp(a,n)
{
    var A:nat := a;
    var N:nat := n;
    R := 1;
    while N > 0
        //invariant exp(A,N)*R == exp(a,n)
        decreases N
    {
        if N % 2 == 0
        {
            A := A * A;
            N := N/2;
        }
        else
        {
            R := R*A;
            N := N-1;
        }
    }
}

ghost method exp_lemma(n:nat, p:nat)
decreases p
ensures exp(n*n,p) == exp(n,2*p)
{
    if p == 0 {} else
    {
        assert exp(n*n,p) == n*n*exp(n*n,p-1);
        exp_lemma(n,p-1);
        assert n*n*exp(n*n,p-1) == n*n*exp(n,2*(p-1));
        assert n*n*exp(n,2*(p-1))==exp(n,2*p);
    }
}

method apn_log(a:nat, n:nat) returns (R:nat)
ensures R==exp(a,n)
{
    var A:nat := a;
    var N:nat := n;
    R := 1;
    while N > 0
        invariant exp(A,N)*R == exp(a,n)
        decreases N
    {
        if N % 2 == 0
        {
            var A0, N0 := A, N;
            var M0:nat := N0 / 2;
            assert N0 == 2*M0;
            exp_lemma(A0,M0);
            assert exp(A0,2*M0) == exp(A0*A0, M0);
            A := A * A;
            N := N/2;
            assert exp(A,N) == exp(A0,N0);
        }
        else
        {
            R := R*A;
            N := N-1;
        }
    }
}
method notin(a: array<int>)
requires (forall i : int :: (i >= 0) && (i < a.Length ) ==> a[i] >= 0)
ensures (forall i : int :: (i >= 0) && (i < a.Length) ==> a[i] == 0)
{
    var i := 0;

    while (i < a.Length)
    invariant(i <= a.Length && i >= 0 && forall k : int :: (k>=0) && (k<i) ==> a[k] == 0)
    decreases(a.Length - i)

    {
        
        while (a[i] > 0)
        invariant(i <= a.Length && i >= 0)
        decreases(i+a[i])
        {
            a[i] := a[i] - 1;
        }
        
        i := i+1;
    }
}
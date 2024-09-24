method notin(a: seq<int>) returns (r: int)
requires true
ensures (forall i : int :: (i >= 0) && (i < |a|) ==> a[i] != r)
{
    
    r := 0;
    var i := 0;

    while (i < |a|)
    invariant(i <= |a| && i >= 0 && forall k : int :: (k>=0) && (k<i) ==> a[k] < r)

    {
        //Find max number in array
        if a[i] >= r{
            r := a[i];
        }
        r := r+1;
        i := i +1; 
        
    }
}

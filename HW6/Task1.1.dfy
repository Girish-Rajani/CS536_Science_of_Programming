method notin(k: int, g: int, b: int) returns (miles: int)
requires k == g && g > 0 && b == 0
ensures miles >= k-1
{
    miles := 0;
    var gas_temp := g;
    var batt_temp := b;

    while (gas_temp > 1 || batt_temp > 0)
    invariant (gas_temp >= 0 && batt_temp >= 0 && miles >= k-(gas_temp+batt_temp))
    decreases (gas_temp + batt_temp)
    {
        if batt_temp > 0
        {
            batt_temp := batt_temp - 1;
        }
        else
        {
            gas_temp := gas_temp - 2;
            batt_temp := batt_temp + 1;
        }
        miles := miles + 1;
    }
}

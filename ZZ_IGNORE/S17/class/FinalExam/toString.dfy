function method intToString(n: int): (s: string)
{
    if (n == 0) then "0" else
    if (n < 0) then "-" + intToStringHelper(n) else
    intToStringHelper(n)
}

function method intToStringHelper(n: int): string
{
    ""
    //intToStringHelper(n/10) + intToDigit(n - n/10*10)
}

function method mod10(n: int): int
{
    n - 10*(n/10)
}

function method intToDigit(n: int): string
{
    if (n==0) then "0" else
    if (n==1) then "1" else
    if (n==2) then "2" else
    if (n==3) then "3" else
    if (n==4) then "4" else
    if (n==5) then "5" else
    if (n==6) then "6" else
    if (n==7) then "7" else
    if (n==8) then "8" else
    if (n==9) then "9" else
    "error"
}

method Main()
{
    print mod10(123);
    assert forall n: nat :: n >= 0 ==> n/10 < 10;
}
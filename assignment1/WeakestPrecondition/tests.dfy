include "submission.dfy"

abstract module Tests {
    import Submission

    @TimeLimit(60)
    method Example(x: int, a: seq<int>) returns (y: int)
        requires Submission.precon0(x, a)
        ensures y < 10 
    {
     if x > 0 {
            y := x + 1;
        } else {
            y := a[0];
        }
    }


    @TimeLimit(60)
    method Book_2_22(x: int) returns (y: int)
        requires Submission.precon1(x)
        ensures y % 2 == 0
    {
        if x < 10 {
            if x < 20 {
                y := 1;
            } else {
                y := 2;
            }
        } else {
            y := 4;
        }
    }

    @TimeLimit(60) 
    method Book_2_23_variant(x: int) returns (y: int, z: int)
        requires Submission.precon2(x)
        ensures y % 2 == 0
    {
        z := 0;
        if x < 8 {
            if x < 4 {
                z := x + 1;
                y := z;
            } else {
                y := 2;
            }
        } else {
            y := x + 2;
            if x < 32 {
                y := 1;
            }
        }
    }

    @TimeLimit(60)
    method Book_2_24(x: int) returns (y: int)
        requires Submission.precon3(x)
        ensures 0 <= y < 100
    {
        if x < 34 {
            if x == 2 {
                y := x + 1;
            } else {
                y := 233;
            }
        } else {
            if x < 55 {
                y := 21;
            } else {
                y := 144;
            }
        }
    }
    
    @TimeLimit(60)
    method Exercise(u: int, a: seq<int>) returns (t: int)
        requires Submission.precon4(u, a)
        ensures t % 2 == 0
    {
        t := a[u+1];
        t := t + 4;
    }
}
// Please, before you do anything else, add your names here:
// Group:    <Group number>
// Member 1: <Full name 1>: <Student number 1>
// Member 2: <Full name 2>: <Student number 2>

include "assignment.dfy" 

module Submission refines Assignment {
    // example
    ghost predicate precon0(x: int, a: seq<int>) {
        // copied from precon0_calc
        x < 9  && (x <= 0 ==> |a| > 0 && a[0] < 10)
    }

    ghost predicate precon1(x: int)

    ghost predicate precon2(x: int)

    ghost predicate precon3(x: int)

    ghost predicate precon4(u: int, a: seq<int>)
    
    // example
    method precon0_calc(x: int, a: seq<int>) returns (y: int)
        requires precon0(x, a) 
    {
        // following line is the calculated wp; copy this to precon0
        assert x < 9  && (x <= 0 ==> |a| > 0 && a[0] < 10);
        assert (x > 0 ==> x < 9) && (x <= 0 ==> |a| > 0 && a[0] < 10);
        if x > 0 {
            assert x < 9;
            assert x + 1 < 10;
            y := x + 1;
            assert y < 10;
        } else {
            assert |a| > 0 && a[0] < 10;
            y := a[0];
            assert y < 10;
        }
        assert y < 10;
    }

    method precon1_calc(x: int) returns (y: int)
      requires precon1(x) 
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
        assert y % 2 == 0; 
    }

    method precon2_calc(x: int) returns (y: int, z: int)
        requires precon2(x)
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
        assert y % 2 == 0;
    }

    method precon3_calc(x: int) returns (y: int)
        requires precon3(x)
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
        assert 0 <= y < 100;
    }

    method precon4_calc(u: int, a: seq<int>) returns (t: int)
        requires precon4(u, a)
    {
        t := a[u+1];
        t := t + 4;
        assert t % 2 == 0;
    }
}

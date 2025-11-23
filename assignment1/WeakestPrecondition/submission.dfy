// Please, before you do anything else, add your names here:
// Group:    69
// Member 1: Dominika Orzechowska: 2098199
//  Member 2:  Jort Kuipers 2111446

include "assignment.dfy"

module Submission refines Assignment {
  // example
  ghost predicate precon0(x: int, a: seq<int>) {
    // copied from precon0_calc
    x < 9  && (x <= 0 ==> |a| > 0 && a[0] < 10)
  }

  ghost predicate precon1(x: int) {
    !(x < 10)
    //((x < 10) ==> (((x<20) ==> 1 % 2 == 0) && (!(x<20) ==> 2 % 2 == 0) )) && ((!(x < 10) ==> (4 % 2 == 0)))
  }

  ghost predicate precon2(x: int){
    ( (x >= 4) || ((x + 1) % 2 == 0) ) && ( (x < 8) || (x % 2 == 0 && x >= 32) )
    //( (x < 8) ==> ( (x >= 4) || ((x + 1) % 2 == 0) ) ) && ( !(x < 8) ==> ((x + 2) % 2 == 0 && x >= 32) )
    //((x < 8)==> ((x < 4) ==> (x + 1) % 2 == 0) ) && ( (x < 8) ==> (!(x < 4) ==> 2 % 2 ==0) ) && ( !(x < 8) ==> ( (x + 2) % 2 == 0 && ( (x < 32) ==> (1 % 2 ==0) ) ) )
  }

  ghost predicate precon3(x: int){
    x == 2 || (34 <= x < 55)
  }

  ghost predicate precon4(u: int, a: seq<int>){
    (0 <= u+1 < |a|) && (a[u+1] % 2 == 0)
  }

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
    assert !(x < 10);
    assert ((x < 10) ==> (((x<20) ==> 1 % 2 == 0) && (!(x<20) ==> 2 % 2 == 0) )) && ((!(x < 10) ==> (4 % 2 == 0)));
    if x < 10 {
      assert false;
      if x < 20 {
        y := 1;
      } else {
        y := 2;
        assert y == 2 * 1;
      }
      assert y % 2 == 0;
    } else {
      y := 4;
    }
    assert y % 2 == 0;
  }

  method precon2_calc(x: int) returns (y: int, z: int)
    requires precon2(x)
  {
    assert ( (x >= 4) || ((x + 1) % 2 == 0) ) && ( (x < 8) || (x % 2 == 0 && x >= 32) );
    assert ( (x >= 8) || (x >= 4) || ((x + 1) % 2 == 0) ) && ( (x < 8) || (x % 2 == 0 && x >= 32) );
    assert ( (x < 8) ==> ( (x >= 4) || ((x + 1) % 2 == 0) ) ) && ( !(x < 8) ==> ((x + 2) % 2 == 0 && x >= 32) );
    assert ( (x < 8) ==> ((x < 4) ==> (x + 1) % 2 == 0) ) && ( (x < 8) ==> (!(x < 4) ==> 2 % 2 == 0) ) && ( !(x < 8) ==> ( (x + 2) % 2 == 0 && ( (x < 32) ==> (1 % 2 == 0) ) ) );

    z := 0;
    if x < 8 {
      assert ( (x >= 4) || ((x + 1) % 2 == 0) );
      assert ( (x >= 4) || ((x + 1) % 2 == 0) ) && ( true );
      assert ( (x >= 4) || ((x + 1) % 2 == 0) ) && ( (x < 4) || true );
      assert ( (x >= 4) || ((x + 1) % 2 == 0) ) && ( (x < 4) || (2 % 2 ==0) );
      assert ( !(x < 4) || ((x + 1) % 2 == 0) ) && ( (x < 4) || (2 % 2 ==0) );
      assert (x < 4) ==> (x + 1) % 2 == 0 && (!(x < 4) ==> 2 % 2 ==0);
      if x < 4 {
        assert (x + 1) % 2 == 0;
        z := x + 1;
        y := z;
        assert y % 2 == 0;
      } else {
        assert 2 % 2 == 0;
        y := 2;
        assert y % 2 == 0;
      }
    } else {
      assert (x + 2) % 2 == 0 && x >= 32;
      assert (x + 2) % 2 == 0 && (x >= 32 || false);
      assert (x + 2) % 2 == 0 && (x < 32) ==> 1 % 2 == 0;
      y := x + 2;

      if x < 32 {
        assert 1 % 2 == 0;
        y := 1;
        assert !(y % 2 == 0);
      }
    }
    assert y % 2 == 0;
  }

  method precon3_calc(x: int) returns (y: int)
    requires precon3(x)
  {

    assert x == 2 || (34 <= x < 55);
    assert ((x >= 34 || x == 2)) && (x < 55);
    assert ((x >= 34 || x == 2)) && ((x < 34) || (x < 55));
    assert ((x >= 34 || x == 2)) && (!(x >= 34) || (x < 55));
    assert (x == 2 ==> (0 <= x + 1 < 100)) && ((34 <= x < 55) ==> (0 <= 21 < 100));
    if x < 34 {
      assert x == 2;
      assert ((x == 2) ==> true) && (!(x == 2) ==> false);
      if x == 2 {
        assert true;
        assert 0 <= 3 < 100;
        assert 0 <= x + 1 < 100;
        y := x + 1;
        assert 0 <= y < 100;

      } else {
        assert false;
        y := 233;
      }
    } else {
      assert x < 55;
      if x < 55 {
        assert true;
        assert 0 <= 21 < 100;
        y := 21;
        assert 0 <= y < 100;
      } else {
        assert false;
        y := 144;
      }
    }
    assert 0 <= y < 100;
  }

  method precon4_calc(u: int, a: seq<int>) returns (t: int)
    requires precon4(u, a)
  {
    assert (0 <= u+1 < |a|) && (a[u+1] % 2 == 0);
    t := a[u+1];
    assert (t + 4) % 2 == 0;
    t := t + 4;
    assert t % 2 == 0;
  }

}

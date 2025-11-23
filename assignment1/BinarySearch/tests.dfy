include "submission.dfy"

abstract module Tests {
  import Submission

  @TimeLimit(60)
  method BinSearchTest0() {
    var a := [1, 3, 2, 4, 5, 6];
    var h;
    h := Submission.BinSearchSegment(a, 2, 0, 1);
    assert a[h] <= 2;
    assert a[h+1] > 2;
    assert h == 0;
  }

  @TimeLimit(60)
  method BinSearchTest1() {
    var a := [1, 3, 2, 4, 6, 8];
    var h;
    h := Submission.BinSearchSegment(a, 4, 0, |a|-1);
    assert h == 3; 
  }

  @TimeLimit(60)
  method BinSearchTest2() {
    var a := [1, 3, 2, 4, 6, 8];
    var h;
    h := Submission.BinSearchSegment(a, 5, 0, |a|-1);
    assert h == 3;
  }

  @TimeLimit(60)
  method BinSearchTest3() {
    var a := [1, 3, 2, 4, 6, 8];
    var h;
    h := Submission.BinSearchSegment(a, 2, 0, |a|-1);
    assert h == 0 || h == 2;
  }

}
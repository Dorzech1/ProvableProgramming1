module Predef {
    // no definitions for this question
}

abstract module Assignment refines Predef { 
    ghost predicate precon0(x: int, a: seq<int>)
    ghost predicate precon1(x: int)
    ghost predicate precon2(x: int)
    ghost predicate precon3(x: int)
    ghost predicate precon4(u: int, a: seq<int>)
} 
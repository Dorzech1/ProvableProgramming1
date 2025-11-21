// Please, before you do anything else, add your names here:
// Group:    69
// Member 1:  Dominika Orzechowska: 2098199
// Member 2:  Jort Kuipers 2111446

include "assignment.dfy"
 
/**
    Add preconditions (requires) and postconditions (ensures) and an implementation (body) 
    to this method.
    Make sure this file and the file tests.dfy verify.
    Verification of tests.dfy is only dependent on the contract of this method, 
    not on its implementation. 
 */
module Submission refines Assignment {
    // Note that while you CAN remove this time limit, we will put it back when
    // we start grading. Please leave it in and use it as a guide. Submissions
    // that time out are considered wrong.
    @TimeLimit(60)
    method BinSearchSegment(a: seq<int>, key: int, lo: nat, hi: nat) returns (here: nat)
        decreases hi - lo // keep this line
        // TODO 

}

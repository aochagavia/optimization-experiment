# How can I tackle this optimization problem in Z3?

## Context

As a way to learn more about optimization, I am trying to solve an optimization problem. I have modelled the problem in [Z3](https://github.com/Z3Prover/z3), but I think I might be doing something wrong, because it takes seconds to solve even in small instances and minutes in realistic scenarios. I feel like I must be missing something.

My questions are:

* Is it normal that this problem is so slow to solve? I have no previous experience, so maybe this is just how it is.
* Is Z3 the right tool for the job?
* Do you have any general suggestions on how to tackle this problem?

## Description of the optimization problem

I am organizing a cooking workshop. There are `i` teachers, `j` students and `k` practical assignments. For each practical assignment, students need to be divided in `i` groups, so they can work on the assignment under the supervision of a teacher. There are two additional requirements:

* Every teacher **must** teach every student
* We want to **maximize** the amount of students that get to know each other during the assignments (i.e. the amount of pairs of students that have worked together in at least one assignment)

For instance, with 2 teachers, 6 students and 2 lab assignments, you could get the following division:

Assignment 1:

* Teacher 1: student 1, student 2, student 3
* Teacher 2: student 4, student 5, student 6

Assignment 2:

* Teacher 1: student 4, student 5, student 6
* Teacher 2: student 1, student 2, student 3

Here, we have a division where every teacher has taught every student. However, by necessity that means that the amount of students that got to know each other is low, since the groups did not change between assignment 1 and 2.

## Explaining the problem to Z3

I wrote a program to generate a bunch of SMT-LIB 2.0 statements, which are then fed into Z3. For the previous example, we get the following code:

Define a helper function to count ones in a `BitVec`, since Z3 does not have a builtin function for that:

    (define-fun countOnes ((x (_ BitVec 6))) Int (bv2int (bvadd (ite (= #b1 ((_ extract 0 0) x)) #b000001 #b000000)(ite (= #b1 ((_ extract 1 1) x)) #b000001 #b000000)(ite (= #b1 ((_ extract 2 2) x)) #b000001 #b000000)(ite (= #b1 ((_ extract 3 3) x)) #b000001 #b000000)(ite (= #b1 ((_ extract 4 4) x)) #b000001 #b000000)(ite (= #b1 ((_ extract 5 5) x)) #b000001 #b000000))))

Declare constants in the form `s{x}_a{y}_t{z}` that indicate whether student `x` is doing assignment `y` with teacher `z`:

    (declare-const s1_a1_t1 Bool)
    (declare-const s1_a1_t2 Bool)
    (declare-const s1_a2_t1 Bool)
    (declare-const s1_a2_t2 Bool)
    (declare-const s2_a1_t1 Bool)
    (declare-const s2_a1_t2 Bool)
    (declare-const s2_a2_t1 Bool)
    (declare-const s2_a2_t2 Bool)
    (declare-const s3_a1_t1 Bool)
    (declare-const s3_a1_t2 Bool)
    (declare-const s3_a2_t1 Bool)
    (declare-const s3_a2_t2 Bool)
    (declare-const s4_a1_t1 Bool)
    (declare-const s4_a1_t2 Bool)
    (declare-const s4_a2_t1 Bool)
    (declare-const s4_a2_t2 Bool)
    (declare-const s5_a1_t1 Bool)
    (declare-const s5_a1_t2 Bool)
    (declare-const s5_a2_t1 Bool)
    (declare-const s5_a2_t2 Bool)
    (declare-const s6_a1_t1 Bool)
    (declare-const s6_a1_t2 Bool)
    (declare-const s6_a2_t1 Bool)
    (declare-const s6_a2_t2 Bool)

Declare constraints to ensure that, for every assignment, a student should work under the supervision of exactly one teacher:

    (assert (= 1 (+ (ite s1_a1_t1 1 0) (ite s1_a1_t2 1 0) )))
    (assert (= 1 (+ (ite s1_a2_t1 1 0) (ite s1_a2_t2 1 0) )))
    (assert (= 1 (+ (ite s2_a1_t1 1 0) (ite s2_a1_t2 1 0) )))
    (assert (= 1 (+ (ite s2_a2_t1 1 0) (ite s2_a2_t2 1 0) )))
    (assert (= 1 (+ (ite s3_a1_t1 1 0) (ite s3_a1_t2 1 0) )))
    (assert (= 1 (+ (ite s3_a2_t1 1 0) (ite s3_a2_t2 1 0) )))
    (assert (= 1 (+ (ite s4_a1_t1 1 0) (ite s4_a1_t2 1 0) )))
    (assert (= 1 (+ (ite s4_a2_t1 1 0) (ite s4_a2_t2 1 0) )))
    (assert (= 1 (+ (ite s5_a1_t1 1 0) (ite s5_a1_t2 1 0) )))
    (assert (= 1 (+ (ite s5_a2_t1 1 0) (ite s5_a2_t2 1 0) )))
    (assert (= 1 (+ (ite s6_a1_t1 1 0) (ite s6_a1_t2 1 0) )))
    (assert (= 1 (+ (ite s6_a2_t1 1 0) (ite s6_a2_t2 1 0) )))

Declare constraints to ensure that every teacher must teach every student at least once:

    (assert (or s1_a1_t1 s1_a2_t1 ))
    (assert (or s2_a1_t1 s2_a2_t1 ))
    (assert (or s3_a1_t1 s3_a2_t1 ))
    (assert (or s4_a1_t1 s4_a2_t1 ))
    (assert (or s5_a1_t1 s5_a2_t1 ))
    (assert (or s6_a1_t1 s6_a2_t1 ))
    (assert (or s1_a1_t2 s1_a2_t2 ))
    (assert (or s2_a1_t2 s2_a2_t2 ))
    (assert (or s3_a1_t2 s3_a2_t2 ))
    (assert (or s4_a1_t2 s4_a2_t2 ))
    (assert (or s5_a1_t2 s5_a2_t2 ))
    (assert (or s6_a1_t2 s6_a2_t2 ))

Declare constraints to ensure that, for each assignment, a teacher must teach at least 3 students:

    (assert (>= 3 (+ (ite s1_a1_t1 1 0) (ite s2_a1_t1 1 0) (ite s3_a1_t1 1 0) (ite s4_a1_t1 1 0) (ite s5_a1_t1 1 0) (ite s6_a1_t1 1 0) )))
    (assert (>= 3 (+ (ite s1_a2_t1 1 0) (ite s2_a2_t1 1 0) (ite s3_a2_t1 1 0) (ite s4_a2_t1 1 0) (ite s5_a2_t1 1 0) (ite s6_a2_t1 1 0) )))
    (assert (>= 3 (+ (ite s1_a1_t2 1 0) (ite s2_a1_t2 1 0) (ite s3_a1_t2 1 0) (ite s4_a1_t2 1 0) (ite s5_a1_t2 1 0) (ite s6_a1_t2 1 0) )))
    (assert (>= 3 (+ (ite s1_a2_t2 1 0) (ite s2_a2_t2 1 0) (ite s3_a2_t2 1 0) (ite s4_a2_t2 1 0) (ite s5_a2_t2 1 0) (ite s6_a2_t2 1 0) )))

Declare functions to keep track of which students have worked together for an assignment:

TODO: rename s1 to something more descriptive, like s1_students_met
TODO: use functions instead of const + assert (and test whether it makes any difference)

    (declare-const s1 (_ BitVec 6))
    (declare-const s2 (_ BitVec 6))
    (declare-const s3 (_ BitVec 6))
    (declare-const s4 (_ BitVec 6))
    (declare-const s5 (_ BitVec 6))
    (declare-const s6 (_ BitVec 6))

Constraints to ... Hmmm, these could actually be functions!

(assert (= s1 (bvor (ite s1_a1_t1 (ite s1_a1_t1 #b100000 #b000000) #b000000)(ite s1_a1_t2 (ite s1_a1_t2 #b100000 #b000000) #b000000)(ite s1_a2_t1 (ite s1_a2_t1 #b100000 #b000000) #b000000)(ite s1_a2_t2 (ite s1_a2_t2 #b100000 #b000000) #b000000)(ite s1_a1_t1 (ite s2_a1_t1 #b010000 #b000000) #b000000)(ite s1_a1_t2 (ite s2_a1_t2 #b010000 #b000000) #b000000)(ite s1_a2_t1 (ite s2_a2_t1 #b010000 #b000000) #b000000)(ite s1_a2_t2 (ite s2_a2_t2 #b010000 #b000000) #b000000)(ite s1_a1_t1 (ite s3_a1_t1 #b001000 #b000000) #b000000)(ite s1_a1_t2 (ite s3_a1_t2 #b001000 #b000000) #b000000)(ite s1_a2_t1 (ite s3_a2_t1 #b001000 #b000000) #b000000)(ite s1_a2_t2 (ite s3_a2_t2 #b001000 #b000000) #b000000)(ite s1_a1_t1 (ite s4_a1_t1 #b000100 #b000000) #b000000)(ite s1_a1_t2 (ite s4_a1_t2 #b000100 #b000000) #b000000)(ite s1_a2_t1 (ite s4_a2_t1 #b000100 #b000000) #b000000)(ite s1_a2_t2 (ite s4_a2_t2 #b000100 #b000000) #b000000)(ite s1_a1_t1 (ite s5_a1_t1 #b000010 #b000000) #b000000)(ite s1_a1_t2 (ite s5_a1_t2 #b000010 #b000000) #b000000)(ite s1_a2_t1 (ite s5_a2_t1 #b000010 #b000000) #b000000)(ite s1_a2_t2 (ite s5_a2_t2 #b000010 #b000000) #b000000)(ite s1_a1_t1 (ite s6_a1_t1 #b000001 #b000000) #b000000)(ite s1_a1_t2 (ite s6_a1_t2 #b000001 #b000000) #b000000)(ite s1_a2_t1 (ite s6_a2_t1 #b000001 #b000000) #b000000)(ite s1_a2_t2 (ite s6_a2_t2 #b000001 #b000000) #b000000))))
(assert (= s2 (bvor (ite s2_a1_t1 (ite s1_a1_t1 #b100000 #b000000) #b000000)(ite s2_a1_t2 (ite s1_a1_t2 #b100000 #b000000) #b000000)(ite s2_a2_t1 (ite s1_a2_t1 #b100000 #b000000) #b000000)(ite s2_a2_t2 (ite s1_a2_t2 #b100000 #b000000) #b000000)(ite s2_a1_t1 (ite s2_a1_t1 #b010000 #b000000) #b000000)(ite s2_a1_t2 (ite s2_a1_t2 #b010000 #b000000) #b000000)(ite s2_a2_t1 (ite s2_a2_t1 #b010000 #b000000) #b000000)(ite s2_a2_t2 (ite s2_a2_t2 #b010000 #b000000) #b000000)(ite s2_a1_t1 (ite s3_a1_t1 #b001000 #b000000) #b000000)(ite s2_a1_t2 (ite s3_a1_t2 #b001000 #b000000) #b000000)(ite s2_a2_t1 (ite s3_a2_t1 #b001000 #b000000) #b000000)(ite s2_a2_t2 (ite s3_a2_t2 #b001000 #b000000) #b000000)(ite s2_a1_t1 (ite s4_a1_t1 #b000100 #b000000) #b000000)(ite s2_a1_t2 (ite s4_a1_t2 #b000100 #b000000) #b000000)(ite s2_a2_t1 (ite s4_a2_t1 #b000100 #b000000) #b000000)(ite s2_a2_t2 (ite s4_a2_t2 #b000100 #b000000) #b000000)(ite s2_a1_t1 (ite s5_a1_t1 #b000010 #b000000) #b000000)(ite s2_a1_t2 (ite s5_a1_t2 #b000010 #b000000) #b000000)(ite s2_a2_t1 (ite s5_a2_t1 #b000010 #b000000) #b000000)(ite s2_a2_t2 (ite s5_a2_t2 #b000010 #b000000) #b000000)(ite s2_a1_t1 (ite s6_a1_t1 #b000001 #b000000) #b000000)(ite s2_a1_t2 (ite s6_a1_t2 #b000001 #b000000) #b000000)(ite s2_a2_t1 (ite s6_a2_t1 #b000001 #b000000) #b000000)(ite s2_a2_t2 (ite s6_a2_t2 #b000001 #b000000) #b000000))))
(assert (= s3 (bvor (ite s3_a1_t1 (ite s1_a1_t1 #b100000 #b000000) #b000000)(ite s3_a1_t2 (ite s1_a1_t2 #b100000 #b000000) #b000000)(ite s3_a2_t1 (ite s1_a2_t1 #b100000 #b000000) #b000000)(ite s3_a2_t2 (ite s1_a2_t2 #b100000 #b000000) #b000000)(ite s3_a1_t1 (ite s2_a1_t1 #b010000 #b000000) #b000000)(ite s3_a1_t2 (ite s2_a1_t2 #b010000 #b000000) #b000000)(ite s3_a2_t1 (ite s2_a2_t1 #b010000 #b000000) #b000000)(ite s3_a2_t2 (ite s2_a2_t2 #b010000 #b000000) #b000000)(ite s3_a1_t1 (ite s3_a1_t1 #b001000 #b000000) #b000000)(ite s3_a1_t2 (ite s3_a1_t2 #b001000 #b000000) #b000000)(ite s3_a2_t1 (ite s3_a2_t1 #b001000 #b000000) #b000000)(ite s3_a2_t2 (ite s3_a2_t2 #b001000 #b000000) #b000000)(ite s3_a1_t1 (ite s4_a1_t1 #b000100 #b000000) #b000000)(ite s3_a1_t2 (ite s4_a1_t2 #b000100 #b000000) #b000000)(ite s3_a2_t1 (ite s4_a2_t1 #b000100 #b000000) #b000000)(ite s3_a2_t2 (ite s4_a2_t2 #b000100 #b000000) #b000000)(ite s3_a1_t1 (ite s5_a1_t1 #b000010 #b000000) #b000000)(ite s3_a1_t2 (ite s5_a1_t2 #b000010 #b000000) #b000000)(ite s3_a2_t1 (ite s5_a2_t1 #b000010 #b000000) #b000000)(ite s3_a2_t2 (ite s5_a2_t2 #b000010 #b000000) #b000000)(ite s3_a1_t1 (ite s6_a1_t1 #b000001 #b000000) #b000000)(ite s3_a1_t2 (ite s6_a1_t2 #b000001 #b000000) #b000000)(ite s3_a2_t1 (ite s6_a2_t1 #b000001 #b000000) #b000000)(ite s3_a2_t2 (ite s6_a2_t2 #b000001 #b000000) #b000000))))
(assert (= s4 (bvor (ite s4_a1_t1 (ite s1_a1_t1 #b100000 #b000000) #b000000)(ite s4_a1_t2 (ite s1_a1_t2 #b100000 #b000000) #b000000)(ite s4_a2_t1 (ite s1_a2_t1 #b100000 #b000000) #b000000)(ite s4_a2_t2 (ite s1_a2_t2 #b100000 #b000000) #b000000)(ite s4_a1_t1 (ite s2_a1_t1 #b010000 #b000000) #b000000)(ite s4_a1_t2 (ite s2_a1_t2 #b010000 #b000000) #b000000)(ite s4_a2_t1 (ite s2_a2_t1 #b010000 #b000000) #b000000)(ite s4_a2_t2 (ite s2_a2_t2 #b010000 #b000000) #b000000)(ite s4_a1_t1 (ite s3_a1_t1 #b001000 #b000000) #b000000)(ite s4_a1_t2 (ite s3_a1_t2 #b001000 #b000000) #b000000)(ite s4_a2_t1 (ite s3_a2_t1 #b001000 #b000000) #b000000)(ite s4_a2_t2 (ite s3_a2_t2 #b001000 #b000000) #b000000)(ite s4_a1_t1 (ite s4_a1_t1 #b000100 #b000000) #b000000)(ite s4_a1_t2 (ite s4_a1_t2 #b000100 #b000000) #b000000)(ite s4_a2_t1 (ite s4_a2_t1 #b000100 #b000000) #b000000)(ite s4_a2_t2 (ite s4_a2_t2 #b000100 #b000000) #b000000)(ite s4_a1_t1 (ite s5_a1_t1 #b000010 #b000000) #b000000)(ite s4_a1_t2 (ite s5_a1_t2 #b000010 #b000000) #b000000)(ite s4_a2_t1 (ite s5_a2_t1 #b000010 #b000000) #b000000)(ite s4_a2_t2 (ite s5_a2_t2 #b000010 #b000000) #b000000)(ite s4_a1_t1 (ite s6_a1_t1 #b000001 #b000000) #b000000)(ite s4_a1_t2 (ite s6_a1_t2 #b000001 #b000000) #b000000)(ite s4_a2_t1 (ite s6_a2_t1 #b000001 #b000000) #b000000)(ite s4_a2_t2 (ite s6_a2_t2 #b000001 #b000000) #b000000))))
(assert (= s5 (bvor (ite s5_a1_t1 (ite s1_a1_t1 #b100000 #b000000) #b000000)(ite s5_a1_t2 (ite s1_a1_t2 #b100000 #b000000) #b000000)(ite s5_a2_t1 (ite s1_a2_t1 #b100000 #b000000) #b000000)(ite s5_a2_t2 (ite s1_a2_t2 #b100000 #b000000) #b000000)(ite s5_a1_t1 (ite s2_a1_t1 #b010000 #b000000) #b000000)(ite s5_a1_t2 (ite s2_a1_t2 #b010000 #b000000) #b000000)(ite s5_a2_t1 (ite s2_a2_t1 #b010000 #b000000) #b000000)(ite s5_a2_t2 (ite s2_a2_t2 #b010000 #b000000) #b000000)(ite s5_a1_t1 (ite s3_a1_t1 #b001000 #b000000) #b000000)(ite s5_a1_t2 (ite s3_a1_t2 #b001000 #b000000) #b000000)(ite s5_a2_t1 (ite s3_a2_t1 #b001000 #b000000) #b000000)(ite s5_a2_t2 (ite s3_a2_t2 #b001000 #b000000) #b000000)(ite s5_a1_t1 (ite s4_a1_t1 #b000100 #b000000) #b000000)(ite s5_a1_t2 (ite s4_a1_t2 #b000100 #b000000) #b000000)(ite s5_a2_t1 (ite s4_a2_t1 #b000100 #b000000) #b000000)(ite s5_a2_t2 (ite s4_a2_t2 #b000100 #b000000) #b000000)(ite s5_a1_t1 (ite s5_a1_t1 #b000010 #b000000) #b000000)(ite s5_a1_t2 (ite s5_a1_t2 #b000010 #b000000) #b000000)(ite s5_a2_t1 (ite s5_a2_t1 #b000010 #b000000) #b000000)(ite s5_a2_t2 (ite s5_a2_t2 #b000010 #b000000) #b000000)(ite s5_a1_t1 (ite s6_a1_t1 #b000001 #b000000) #b000000)(ite s5_a1_t2 (ite s6_a1_t2 #b000001 #b000000) #b000000)(ite s5_a2_t1 (ite s6_a2_t1 #b000001 #b000000) #b000000)(ite s5_a2_t2 (ite s6_a2_t2 #b000001 #b000000) #b000000))))
(assert (= s6 (bvor (ite s6_a1_t1 (ite s1_a1_t1 #b100000 #b000000) #b000000)(ite s6_a1_t2 (ite s1_a1_t2 #b100000 #b000000) #b000000)(ite s6_a2_t1 (ite s1_a2_t1 #b100000 #b000000) #b000000)(ite s6_a2_t2 (ite s1_a2_t2 #b100000 #b000000) #b000000)(ite s6_a1_t1 (ite s2_a1_t1 #b010000 #b000000) #b000000)(ite s6_a1_t2 (ite s2_a1_t2 #b010000 #b000000) #b000000)(ite s6_a2_t1 (ite s2_a2_t1 #b010000 #b000000) #b000000)(ite s6_a2_t2 (ite s2_a2_t2 #b010000 #b000000) #b000000)(ite s6_a1_t1 (ite s3_a1_t1 #b001000 #b000000) #b000000)(ite s6_a1_t2 (ite s3_a1_t2 #b001000 #b000000) #b000000)(ite s6_a2_t1 (ite s3_a2_t1 #b001000 #b000000) #b000000)(ite s6_a2_t2 (ite s3_a2_t2 #b001000 #b000000) #b000000)(ite s6_a1_t1 (ite s4_a1_t1 #b000100 #b000000) #b000000)(ite s6_a1_t2 (ite s4_a1_t2 #b000100 #b000000) #b000000)(ite s6_a2_t1 (ite s4_a2_t1 #b000100 #b000000) #b000000)(ite s6_a2_t2 (ite s4_a2_t2 #b000100 #b000000) #b000000)(ite s6_a1_t1 (ite s5_a1_t1 #b000010 #b000000) #b000000)(ite s6_a1_t2 (ite s5_a1_t2 #b000010 #b000000) #b000000)(ite s6_a2_t1 (ite s5_a2_t1 #b000010 #b000000) #b000000)(ite s6_a2_t2 (ite s5_a2_t2 #b000010 #b000000) #b000000)(ite s6_a1_t1 (ite s6_a1_t1 #b000001 #b000000) #b000000)(ite s6_a1_t2 (ite s6_a1_t2 #b000001 #b000000) #b000000)(ite s6_a2_t1 (ite s6_a2_t1 #b000001 #b000000) #b000000)(ite s6_a2_t2 (ite s6_a2_t2 #b000001 #b000000) #b000000))))

Maximize the amount of students that have worked together at least once

    (maximize (+ (countOnes s1)(countOnes s2)(countOnes s3)(countOnes s4)(countOnes s5)(countOnes s6)))

## Limitations

TODO: Specify clearly how it doesn't scale
TODO: Does it run for too long? Which parameters trigger it?

## Future research

TODO: write

Using a linear solver
Using a SAT solver
Using a custom-built solver
Randomize... Not very successful
Ask you!
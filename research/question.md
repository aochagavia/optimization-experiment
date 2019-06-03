## Context

As a way to learn more about SMT solving and optimization, I am trying to solve a concrete problem using [Z3](https://github.com/Z3Prover/z3). I have successfully modelled the problem (it compiles and runs), but I think I might be doing something wrong, because it takes seconds to solve even in small instances and minutes in realistic scenarios. I feel like I must be missing something.

My questions are:

* Is it normal that this problem takes so much time to solve? I have no previous experience, so maybe this is just how it is.
* Is Z3 the right tool for the job? If not, what else would you recommend me to try?

## Description of the optimization problem

Imagine you are organizing a cooking workshop. There are `i` teachers, `j` students and `k` practical assignments. For each practical assignment, students need to be divided in `i` groups, so they can work on the assignment under the supervision of a teacher. There are two additional requirements:

* Every teacher **must** teach every student at least once
* We want to **maximize** the amount of students that get to know each other during the assignments (i.e. the amount of pairs of students that have worked together in at least one assignment)

For instance, with 2 teachers, 6 students and 2 lab assignments, you could get the following division:

Assignment 1:

* Teacher 1: student 1, student 2, student 3
* Teacher 2: student 4, student 5, student 6

Assignment 2:

* Teacher 1: student 4, student 5, student 6
* Teacher 2: student 1, student 2, student 3

Here, every teacher has taught every student. However, by necessity that means that the amount of students that got to know each other is low. In fact, the groups did not change between assignment 1 and 2, only the teachers did.

## Explaining the problem to Z3

I wrote a program to generate a bunch of SMT-LIB statements, which are then fed into Z3. For the previous example with 6 students, 2 teachers and 2 assignments, we get the following code (you can also check it out [here](https://gist.github.com/aochagavia/5138e441b86c2dc0a25bac2413ce932c), if you prefer):

Define a helper function to turn boolean values into integers:

    (define-fun bool2int ((x Bool)) Int (ite x 1 0))

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

    (assert (= 1 (+ (bool2int s1_a1_t1) (bool2int s1_a1_t2) )))
    (assert (= 1 (+ (bool2int s1_a2_t1) (bool2int s1_a2_t2) )))
    (assert (= 1 (+ (bool2int s2_a1_t1) (bool2int s2_a1_t2) )))
    (assert (= 1 (+ (bool2int s2_a2_t1) (bool2int s2_a2_t2) )))
    (assert (= 1 (+ (bool2int s3_a1_t1) (bool2int s3_a1_t2) )))
    (assert (= 1 (+ (bool2int s3_a2_t1) (bool2int s3_a2_t2) )))
    (assert (= 1 (+ (bool2int s4_a1_t1) (bool2int s4_a1_t2) )))
    (assert (= 1 (+ (bool2int s4_a2_t1) (bool2int s4_a2_t2) )))
    (assert (= 1 (+ (bool2int s5_a1_t1) (bool2int s5_a1_t2) )))
    (assert (= 1 (+ (bool2int s5_a2_t1) (bool2int s5_a2_t2) )))
    (assert (= 1 (+ (bool2int s6_a1_t1) (bool2int s6_a1_t2) )))
    (assert (= 1 (+ (bool2int s6_a2_t1) (bool2int s6_a2_t2) )))

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

Declare constraints to ensure that, for each assignment, a teacher must teach exactly 3 students. We use `>=` in combination with `<=` because some instances of the problem allow for a minimum and maximum number of students (i.e. when `j % i != 0`).

    (define-fun t1_a1 () Int (+ (bool2int s1_a1_t1) (bool2int s2_a1_t1) (bool2int s3_a1_t1) (bool2int s4_a1_t1) (bool2int s5_a1_t1) (bool2int s6_a1_t1) ))
    (assert (>= 3 t1_a1))
    (assert (<= 3 t1_a1))
    (define-fun t1_a2 () Int (+ (bool2int s1_a2_t1) (bool2int s2_a2_t1) (bool2int s3_a2_t1) (bool2int s4_a2_t1) (bool2int s5_a2_t1) (bool2int s6_a2_t1) ))
    (assert (>= 3 t1_a2))
    (assert (<= 3 t1_a2))
    (define-fun t2_a1 () Int (+ (bool2int s1_a1_t2) (bool2int s2_a1_t2) (bool2int s3_a1_t2) (bool2int s4_a1_t2) (bool2int s5_a1_t2) (bool2int s6_a1_t2) ))
    (assert (>= 3 t2_a1))
    (assert (<= 3 t2_a1))
    (define-fun t2_a2 () Int (+ (bool2int s1_a2_t2) (bool2int s2_a2_t2) (bool2int s3_a2_t2) (bool2int s4_a2_t2) (bool2int s5_a2_t2) (bool2int s6_a2_t2) ))
    (assert (>= 3 t2_a2))
    (assert (<= 3 t2_a2))

Declare functions to keep track of which students have worked together for an assignment:

    (define-fun s1_has_met_s2 () Bool (or (and s1_a1_t1 s2_a1_t1) (and s1_a2_t1 s2_a2_t1) (and s1_a1_t2 s2_a1_t2) (and s1_a2_t2 s2_a2_t2) ))
    (define-fun s1_has_met_s3 () Bool (or (and s1_a1_t1 s3_a1_t1) (and s1_a2_t1 s3_a2_t1) (and s1_a1_t2 s3_a1_t2) (and s1_a2_t2 s3_a2_t2) ))
    (define-fun s1_has_met_s4 () Bool (or (and s1_a1_t1 s4_a1_t1) (and s1_a2_t1 s4_a2_t1) (and s1_a1_t2 s4_a1_t2) (and s1_a2_t2 s4_a2_t2) ))
    (define-fun s1_has_met_s5 () Bool (or (and s1_a1_t1 s5_a1_t1) (and s1_a2_t1 s5_a2_t1) (and s1_a1_t2 s5_a1_t2) (and s1_a2_t2 s5_a2_t2) ))
    (define-fun s1_has_met_s6 () Bool (or (and s1_a1_t1 s6_a1_t1) (and s1_a2_t1 s6_a2_t1) (and s1_a1_t2 s6_a1_t2) (and s1_a2_t2 s6_a2_t2) ))
    (define-fun s2_has_met_s3 () Bool (or (and s2_a1_t1 s3_a1_t1) (and s2_a2_t1 s3_a2_t1) (and s2_a1_t2 s3_a1_t2) (and s2_a2_t2 s3_a2_t2) ))
    (define-fun s2_has_met_s4 () Bool (or (and s2_a1_t1 s4_a1_t1) (and s2_a2_t1 s4_a2_t1) (and s2_a1_t2 s4_a1_t2) (and s2_a2_t2 s4_a2_t2) ))
    (define-fun s2_has_met_s5 () Bool (or (and s2_a1_t1 s5_a1_t1) (and s2_a2_t1 s5_a2_t1) (and s2_a1_t2 s5_a1_t2) (and s2_a2_t2 s5_a2_t2) ))
    (define-fun s2_has_met_s6 () Bool (or (and s2_a1_t1 s6_a1_t1) (and s2_a2_t1 s6_a2_t1) (and s2_a1_t2 s6_a1_t2) (and s2_a2_t2 s6_a2_t2) ))
    (define-fun s3_has_met_s4 () Bool (or (and s3_a1_t1 s4_a1_t1) (and s3_a2_t1 s4_a2_t1) (and s3_a1_t2 s4_a1_t2) (and s3_a2_t2 s4_a2_t2) ))
    (define-fun s3_has_met_s5 () Bool (or (and s3_a1_t1 s5_a1_t1) (and s3_a2_t1 s5_a2_t1) (and s3_a1_t2 s5_a1_t2) (and s3_a2_t2 s5_a2_t2) ))
    (define-fun s3_has_met_s6 () Bool (or (and s3_a1_t1 s6_a1_t1) (and s3_a2_t1 s6_a2_t1) (and s3_a1_t2 s6_a1_t2) (and s3_a2_t2 s6_a2_t2) ))
    (define-fun s4_has_met_s5 () Bool (or (and s4_a1_t1 s5_a1_t1) (and s4_a2_t1 s5_a2_t1) (and s4_a1_t2 s5_a1_t2) (and s4_a2_t2 s5_a2_t2) ))
    (define-fun s4_has_met_s6 () Bool (or (and s4_a1_t1 s6_a1_t1) (and s4_a2_t1 s6_a2_t1) (and s4_a1_t2 s6_a1_t2) (and s4_a2_t2 s6_a2_t2) ))
    (define-fun s5_has_met_s6 () Bool (or (and s5_a1_t1 s6_a1_t1) (and s5_a2_t1 s6_a2_t1) (and s5_a1_t2 s6_a1_t2) (and s5_a2_t2 s6_a2_t2) ))

Maximize the amount of people that have met:

    (maximize (+ (bool2int s1_has_met_s2)(bool2int s1_has_met_s3)(bool2int s1_has_met_s4)(bool2int s1_has_met_s5)(bool2int s1_has_met_s6)(bool2int s2_has_met_s3)(bool2int s2_has_met_s4)(bool2int s2_has_met_s5)(bool2int s2_has_met_s6)(bool2int s3_has_met_s4)(bool2int s3_has_met_s5)(bool2int s3_has_met_s6)(bool2int s4_has_met_s5)(bool2int s4_has_met_s6)(bool2int s5_has_met_s6)))

## Limitations

The main limitation I am running against is the time it takes to run the models. It just doesn't scale:

* 6 students, 2 teachers, 2 assignments: 100ms
* 7 students, 3 teachers, 3 assignments: 10s
* 9 students, 3 teachers, 3 assignments: killed after a minute (who knows how long it would take...)

My goal is to run this with around 20 students, 3 teachers and 5 assignments... With the current setup, though, I doubt Z3 would ever finish computing that.

[This gist](https://gist.github.com/aochagavia/0aea9d84e353fe416c0c0454cb4e8310) contains the SMT-LIB code for the instance with 9 students, 3 teachers and 3 assignments. To some extent it doesn't surprise me that much to see it taking so long... The function I want to maximize has really exploded in size.

## Closing remarks

As you can see, I am stuck. As far as I know, there is no simpler way of expressing the constraints and the objective function for this problem. It seems to me that I have reached a fundamental limitation. So here go my questions again:

* Is it normal that this problem takes so much time to solve? I have no previous experience, so maybe this is just how it is.
* Is Z3 the right tool for the job? If not, what else would you recommend me to try?

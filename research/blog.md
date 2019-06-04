# An adventure with optimization and Z3

Disclaimer: I partially tell about how I arrived at the solution, but there are many things and
difficulties I don't tell about. Finding the right way to model the problem took some trial and error.

A while ago, a friend presented me an optimization problem that he stumbled upon in his day job.
The problem seemed interesting, so I considered writing a program to solve it, though after a while
I decided to let the occassion pass. The thing is, I don't know that much about optimization and
I had no idea regarding where to start! In the past I have played with linear programming using
the Gurobi solver, but I am no longer a student and licenses are just too expensive. I remember
trying other solvers at the time, but the lack of documentation and difficulties to get them
working on Windows were really off-putting.

That was the situation until I came across [this article](https://codingnest.com/modern-sat-solvers-fast-neat-underused-part-1-of-n/),
where the author explores the amazing world of SAT solvers and comes to the conclusion that they
are criminally underused by the industry. I even read on Hacker News that someone had solved
an Advent of Code puzzle using Z3. While I had heard of Z3 and SAT solvers before, I was convinced
they were more of a research thing, unsuitable for tackling real-world problems. The article
and the comments on Hacker News suggested that I was wrong. Now I had to find out.

<!-- Link to the project on GH. Make sure it has a proper readme, stating that you need Z3 on your path. Explaining how to build and run the Rust program. -->

## The problem

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

In this example, every teacher has taught every student. However, by necessity that means that the amount of students that got to know each other is low. In fact, the groups did not change between assignment 1 and 2, only the teachers did.

## Failed attempt at using Rust's bindings for Z3

These days, my programming language of choice for side projects is Rust. I was happy to find out there are [unofficial Z3 bindings]() for the language. However, when trying them out, I was not able to get them working. Since I had no previous experience with the bindings and the documentation was non-existing, I ended up filing an [issue](https://github.com/prove-rs/z3.rs/issues/29) on GitHub and moved on.

## Building a custom interface to Z3

Even without bindings, I really wanted to use Rust for this project... so instead of switching to a language with working bindings, I set out to find an alternative. It turns out that you can use Z3 as a REPL if to run the binary as `z3 -in`. In practice, this meant that I could generate code on the Rust side, pipe it into Z3's stdin and pipe the responses back from Z3's stdout. A hacky and stringy-typed approach, but it actually worked quite well.

Besides, the best documentation I could find had examples in ...

Advantage, could translate directly from docs in rise4fun!

## Modeling the problem

Declare constants in the form s{x}_a{y}_t{z} that indicate whether student x is doing assignment y with teacher z:

```
(declare-const s1_a1_t1 Bool)
(declare-const s1_a1_t2 Bool)
(declare-const s1_a2_t1 Bool)
(declare-const s1_a2_t2 Bool)
...
(declare-const s6_a1_t1 Bool)
(declare-const s6_a1_t2 Bool)
(declare-const s6_a2_t1 Bool)
(declare-const s6_a2_t2 Bool)
```

Constraint: for every assignment, a student should work under the supervision of exactly one teacher.

Constraint: every teacher must teach every student at least once.

Constraint: for each assignment, every teacher must teach at between `floor(j / i)` and `ceil(j / i)` students

## Asking Z3 to maximize something

Functions to keep track of which students have worked together at least once:

```
(define-fun s1_has_met_s2 () Bool (or (and s1_a1_t1 s2_a1_t1) (and s1_a2_t1 s2_a2_t1) (and s1_a1_t2 s2_a1_t2) (and s1_a2_t2 s2_a2_t2) ))
(define-fun s1_has_met_s3 () Bool (or (and s1_a1_t1 s3_a1_t1) (and s1_a2_t1 s3_a2_t1) (and s1_a1_t2 s3_a1_t2) (and s1_a2_t2 s3_a2_t2) ))
...
(define-fun s5_has_met_s6 () Bool (or (and s5_a1_t1 s6_a1_t1) (and s5_a2_t1 s6_a2_t1) (and s5_a1_t2 s6_a1_t2) (and s5_a2_t2 s6_a2_t2) ))
```

Idea one: ask Z3 to optimize that... Too slow. Really? Maybe I could try again, see if it runs in 5 minutes or something.

Stuck: posted on [SO](https://stackoverflow.com/questions/56418132/how-can-i-best-tackle-this-optimization-problem) (note that the model in the post doesn't match exactly with the final model I exposed above). While I didn't receive the answer I wanted, I got some great tips that helped me come to the model I have now and get some performance boosts.

## Binary search to the rescue!

In the end: binary search (ab)using constraints

Push, pop

## Conclusion

Documentation... Quite obscure that some functions existed. XKCD what did you see! Not really discoverable. On the other hand, interactive thing on rise4fun is great! And docs are quite good for a research project.

MIT licensed! I'm probably going to earn money with this in the future.

Magic! And actually quite easy to use once you get through the first hurdles

Advent of code day 23 of 2019. Maybe the next blog post?

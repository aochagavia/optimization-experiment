mod solution;
mod solver;

use std::error::Error;
use std::fmt::Write;
use std::iter;

use solution::Solution;
use solver::{Satisfiability, Solver};

pub fn student_const(student: usize, round: usize, teacher: usize) -> String {
    format!("s{}_a{}_t{}", student + 1, round + 1, teacher + 1)
}

pub fn student_has_met(student: usize, other_student: usize) -> String {
    format!("s{}_has_met_s{}", student + 1, other_student + 1)
}

pub fn students_in_class(students: usize, teacher: usize, round: usize) -> String {
    let mut output = String::new();
    for student in 0..students {
        output.push_str(&student_const(student, round, teacher));
        output.push(' ');
    }
    output
}

pub fn solve(students: usize, teachers: usize, rounds: usize) -> Result<Solution, Box<dyn Error>> {
    if teachers > rounds {
        return Err("There must at least be as many teachers as rounds, due to our constraints".into());
    }

    let mut input = String::new();

    // Declare a constant for each student, round, teacher combination
    for student in 0..students {
        for round in 0..rounds {
            for teacher in 0..teachers {
                writeln!(input, "(declare-const {} Bool)", student_const(student, round, teacher))?;
            }
        }
    }

    // Constraint: for each round, each student has only one assigned teacher
    let ones: String = iter::repeat("1 ").take(teachers).collect();
    println!("Ones: {}", ones);
    for student in 0..students {
        for round in 0..rounds {
            // `(_ pbeq k c1 c2) x y` means `c1 * x + c2 * y = k`
            // At least 1
            write!(input, "(assert ((_ pbeq 1 {}) ", ones)?;
            for teacher in 0..teachers {
                write!(input, "{} ", student_const(student, round, teacher))?;
            }
            writeln!(input, "))")?;
        }
    }

    // Constraint: every teacher must have taught every student at least once
    for teacher in 0..teachers {
        for student in 0..students {
            write!(input, "(assert (or ")?;
            for round in 0..rounds {
                write!(input, "{} ", student_const(student, round, teacher))?;
            }
            writeln!(input, "))")?;
        }
    }

    dbg!("Alive");

    // Constraint: at a given round, a teacher cannot teach more than max_students or less than min_students
    let max_students = (students as f64 / teachers as f64).ceil() as usize;
    let min_students = students / teachers;
    for teacher in 0..teachers {
        for round in 0..rounds {
            writeln!(input, "(assert ((_ at-most {}) {}))", max_students, students_in_class(students, teacher, round))?;
            writeln!(input, "(assert ((_ at-least {}) {}))", min_students, students_in_class(students, teacher, round))?;
        }
    }

    dbg!("Alive");

    // Functions to calculate how many people met each other
    for student in 0..students {
        for other_student in student + 1..students {
            write!(input, "(define-fun {} () Bool (or ", student_has_met(student, other_student))?;
            for teacher in 0..teachers {
                for round in 0..rounds {
                    write!(input, "(and {} {}) ", student_const(student, round, teacher), student_const(other_student, round, teacher))?;
                }
            }
            writeln!(input, "))")?;
        }
    }

    dbg!("Alive");

    // If `n` is the number of students, then the amount of unique meetings between two people is
    // `n * (n - 1) / 2` (order doesn't matter and we don't count meeting yourself)

    let mut solver = dbg!(Solver::new());
    solver.input("(set-option :timeout 2000)");
    dbg!("Alive");
    println!("{}", input);
    solver.input(&input);
    dbg!("Alive");
    drop(input); // So we don't accidentally try to use it afterwards

    dbg!("Alive");

    let mut min_n = 0;
    let mut max_n = (students * (students - 1)) / 2;
    let mut n;
    let mut last_solution = None;
    println!("Start binary search with min_n = {} and max_n = {}", min_n, max_n);
    while min_n + 1 < max_n {
        n = (min_n + max_n) / 2;

        // Save current state, so we can restore it when we go to the next iteration
        solver.input("(push)");

        let mut assertion = String::new();
        write!(assertion, "(assert ((_ at-least {}) ", n)?;
        for student in 0..students {
            for other_student in student + 1..students {
                write!(assertion, "{} ", student_has_met(student, other_student))?;
            }
        }
        writeln!(assertion, "))")?;
        solver.input(&assertion);

        let sat = solver.check_sat();
        match sat {
            Satisfiability::Sat => {
                min_n = n;
                last_solution = Some(Solution::new(&mut solver, students, teachers, rounds));
            }
            _ => max_n = n,
        }

        println!("n = {}: {:?}", n, sat);

        solver.input("(pop)");
    }

    match last_solution {
        Some(sol) => Ok(sol),
        None => Err("No satisfiable solution found within the given time".into()),
    }
}

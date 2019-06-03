mod solution;
mod solver;

use std::error::Error;
use std::fmt::Write;

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

    // Define a helper function that counts ones in a bit vector of length `students`
    // writeln!(input, "(define-fun bool2int ((x Bool)) Int (ite x 1 0))")?;

    // Declare a constant for each student, round, teacher combination
    for student in 0..students {
        for round in 0..rounds {
            for teacher in 0..teachers {
                writeln!(input, "(declare-const {} Bool)", student_const(student, round, teacher))?;
            }
        }
    }

    // Constraint: for each round, each student has only one assigned teacher
    for student in 0..students {
        for round in 0..rounds {
            // At least 1
            write!(input, "(assert ((_ at-least 1) ")?;
            for teacher in 0..teachers {
                write!(input, "{} ", student_const(student, round, teacher))?;
            }
            writeln!(input, "))")?;

            // At most 1
            write!(input, "(assert ((_ at-most 1) ")?;
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

    // Constraint: at a given round, a teacher cannot teach more than max_students or less than min_students
    let max_students = (students as f64 / teachers as f64).ceil() as usize;
    let min_students = students / teachers;
    for teacher in 0..teachers {
        for round in 0..rounds {
            writeln!(input, "(assert ((_ at-most {}) {}))", max_students, students_in_class(students, teacher, round))?;
            writeln!(input, "(assert ((_ at-least {}) {}))", min_students, students_in_class(students, teacher, round))?;
        }
    }

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

    // Maximize number of meetings
    // write!(input, "(maximize (+ ")?;
    // for student in 0..students {
    //     for other_student in student + 1..students {
    //         write!(input, "(bool2int {})", student_has_met(student, other_student))?;
    //     }
    // }
    // writeln!(input, "))")?;

    // Constrain number of meetings
    // write!(input, "(assert ((_ at-least {}) ")?;
    // for student in 0..students {
    //     for other_student in student + 1..students {
    //         write!(input, "{} ", student_has_met(student, other_student))?;
    //     }
    // }
    // writeln!(input, "))")?;

    // Fire up solver and check sat
    let mut solver = Solver::new();
    // println!("{}", input);
    solver.input("(set-option :timeout 60000)");
    solver.input(&input);
    let sat = solver.check_sat();

    match sat {
        Satisfiability::Unknown => Err("No satisfiable solution found within the given time".into()),
        Satisfiability::Unsat => Err("Unsatisfiable".into()),
        Satisfiability::Sat => Ok(Solution::new(solver)),
    }
}

mod solution;
mod solver;

use std::error::Error;
use std::fmt::Write;
use std::iter;

use solution::Solution;
use solver::{Satisfiability, Solver};

pub fn student_const(student: usize, round: usize, teacher: usize) -> String {
    format!("s{}_r{}_t{}", student, round, teacher)
}

pub fn solve(students: usize, teachers: usize, rounds: usize, minimum_meetings: Option<usize>) -> Result<Solution, Box<dyn Error>> {
    if teachers > rounds {
        return Err("There must at least be as many teachers as rounds, due to our constraints".into());
    }

    let mut input = String::new();

    // Define a helper function that counts ones in a bit vector of length `students`
    let mut zero = String::from("#b");
    zero.extend(iter::repeat('0').take(students));
    let mut one = String::from("#b");
    one.extend(iter::repeat('0').take(students - 1));
    one.push('1');
    write!(input, "(define-fun countOnes ((x (_ BitVec {0}))) Int (bv2int (bvadd ", students)?;
    for bit in 0..students {
        write!(input, "(ite (= #b1 ((_ extract {0} {0}) x)) {1} {2})", bit, one, zero)?;
    }
    writeln!(input, ")))")?;

    // Declare a constant for each student, round, teacher combination
    for student in 0..students {
        for round in 0..rounds {
            for teacher in 0..teachers {
                writeln!(input, "(declare-const {} Bool)", student_const(student, round, teacher))?;
            }
        }
    }

    // Declare a BitVec of people a student has met
    if minimum_meetings.is_some() {
        for student in 0..students {
            writeln!(input, "(declare-const s{} (_ BitVec {}))", student, students)?;
        }
    }

    // Constraint: for each round, each student has only one assigned teacher
    for student in 0..students {
        for round in 0..rounds {
            write!(input, "(assert (= 1 (+ ")?;
            for teacher in 0..teachers {
                write!(input, "(ite {} 1 0) ", student_const(student, round, teacher))?;
            }
            writeln!(input, ")))")?;
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

    // Constraint: at a given round, a teacher cannot teach more than max_students
    let max_students = (students as f64 / teachers as f64).ceil() as usize;
    for teacher in 0..teachers {
        for round in 0..rounds {
            write!(input, "(assert (>= {} (+ ", max_students)?;
            for student in 0..students {
                write!(input, "(ite {} 1 0) ", student_const(student, round, teacher))?;
            }
            writeln!(input, ")))")?;
        }
    }

    // Constraint to calculate how many people met each other
    if let Some(minimum_meetings) = minimum_meetings {
        for student in 0..students {
            write!(input, "(assert (= s{} (bvor ", student)?;
            for other_student in 0..students {
                for round in 0..rounds {
                    for teacher in 0..teachers {
                        let mut other_student_code = String::from("#b");
                        for _ in 0..other_student {
                            other_student_code.push('0');
                        }
                        other_student_code.push('1');
                        for _ in other_student + 1 ..students {
                            other_student_code.push('0');
                        }
                        write!(input, "(ite {} (ite {} {} {3}) {3})", student_const(student, round, teacher), student_const(other_student, round, teacher), other_student_code, zero)?;
                    }
                }
            }
            writeln!(input, ")))")?;
        }

        // Constraint: each student should have met at least 4 other students
        for student in 0..students {
            writeln!(input, "(assert (< {} (countOnes s{})))", minimum_meetings, student)?;
        }
    }

    // Fire up solver and check sat
    let mut solver = Solver::new();
    // println!("{}", input);
    solver.input("(set-option :timeout 10000)");
    solver.input(&input);
    let sat = solver.check_sat();

    match sat {
        Satisfiability::Unknown => Err("No satisfiable solution found within the given time".into()),
        Satisfiability::Unsat => Err("Unsatisfiable".into()),
        Satisfiability::Sat => Ok(Solution::new(solver)),
    }
}

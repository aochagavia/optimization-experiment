mod solver;

use std::error::Error;
use std::fmt::Write;
use std::iter;

use solver::{Satisfiability, Solver};

fn student_const(student: usize, round: usize, teacher: usize) -> String {
    format!("s{}_r{}_t{}", student, round, teacher)
}

fn main() -> Result<(), Box<dyn Error>> {
    let students = vec![
        "Adolfo",
        "Hubert",
        "Tim",
        "Paul",
        "Lodewijk",
        "Mansour",
        "Joost",
        "Tato",
        "Martijn",
        "Everard",
        "Matthijs",
        "Henrik",
        "Remy",
        "Eugen",
        "Fabian",
        "Sebastian",
        "Ben",
    ];

    let teachers = vec![
        "Niko",
        "Jordi",
        "Daniël",
    ];

    let rounds = 3;

    let mut input = String::new();

    // Define a helper function that counts ones in a bit vector of length `students.len()`
    let mut zero = String::from("#b");
    zero.extend(iter::repeat('0').take(students.len()));
    let mut one = String::from("#b");
    one.extend(iter::repeat('0').take(students.len() - 1));
    one.push('1');
    write!(input, "(define-fun countOnes ((x (_ BitVec {0}))) Int (bv2int (bvadd ", students.len())?;
    for bit in 0..students.len() {
        write!(input, "(ite (= #b1 ((_ extract {0} {0}) x)) {1} {2})", bit, one, zero)?;
    }
    writeln!(input, ")))")?;

    // Declare a constant for each student, round, teacher combination
    for student in 0..students.len() {
        for round in 0..rounds {
            for teacher in 0..teachers.len() {
                writeln!(input, "(declare-const {} Bool)", student_const(student, round, teacher))?;
            }
        }
    }

    // Declare a BitVec of people a student has met
    for student in 0..students.len() {
        writeln!(input, "(declare-const s{} (_ BitVec {}))", student, students.len())?;
    }

    // Constraint: for each round, each student has only one assigned teacher
    for student in 0..students.len() {
        for round in 0..rounds {
            write!(input, "(assert (= 1 (+ ")?;
            for teacher in 0..teachers.len() {
                write!(input, "(ite {} 1 0) ", student_const(student, round, teacher))?;
            }
            writeln!(input, ")))")?;
        }
    }

    // Constraint: every teacher must have taught every student at least once
    for teacher in 0..teachers.len() {
        for student in 0..students.len() {
            write!(input, "(assert (or ")?;
            for round in 0..rounds {
                write!(input, "{} ", student_const(student, round, teacher))?;
            }
            writeln!(input, "))")?;
        }
    }

    // Constraint: at a given round, a teacher cannot teach more than max_students
    let max_students = (students.len() as f64 / teachers.len() as f64).ceil() as usize;
    for teacher in 0..teachers.len() {
        for round in 0..rounds {
            write!(input, "(assert (>= {} (+ ", max_students)?;
            for student in 0..students.len() {
                write!(input, "(ite {} 1 0) ", student_const(student, round, teacher))?;
            }
            writeln!(input, ")))")?;
        }
    }

    // Constraint to calculate how many people met each other
    for student in 0..students.len() {
        write!(input, "(assert (= s{} (bvor ", student)?;
        for other_student in 0..students.len() {
            for round in 0..rounds {
                for teacher in 0..teachers.len() {
                    let mut other_student_code = String::from("#b");
                    for _ in 0..other_student {
                        other_student_code.push('0');
                    }
                    other_student_code.push('1');
                    for _ in other_student + 1 ..students.len() {
                        other_student_code.push('0');
                    }
                    write!(input, "(ite {} (ite {} {} {3}) {3})", student_const(student, round, teacher), student_const(other_student, round, teacher), other_student_code, zero)?;
                }
            }
        }
        writeln!(input, ")))")?;
    }

    // Constraint: each student should have met at least 4 other students
    for student in 0..students.len() {
        writeln!(input, "(assert (< 4 (countOnes s{})))", student)?;
    }

    // Fire up solver and check sat
    let mut solver = Solver::new();
    // println!("{}", input);
    solver.input("(set-option :timeout 5000)");
    solver.input(&input);
    let sat = solver.check_sat();

    if sat == Satisfiability::Unknown {
        println!("No satisfiable solution found within the given time");
        return Ok(());
    }
    if sat == Satisfiability::Unsat {
        println!("Unsatisfiable");
        return Ok(());
    }

    // Retrieve variable values
    for round in 0..rounds {
        println!("========");
        println!("Round {}", round);
        println!("========");
        for (teacher, teacher_name) in teachers.iter().enumerate() {
            print!("{}: ", teacher_name);
            for (student, student_name) in students.iter().enumerate() {
                let is_teacher_for_student: bool = solver.eval(student_const(student, round, teacher)).parse().unwrap();
                if is_teacher_for_student {
                    print!("{}, ", student_name);
                }
            }
            println!();
        }

        println!();
    }

    // Retrieve people met
    println!("============");
    println!("Students met");
    println!("============");
    for (student, _) in students.iter().enumerate() {
        let meetings = solver.eval(format!("s{}", student));
        println!("{}: {}", student, meetings);
    }

    Ok(())
}

#[test]
fn shift_left() {
    let x = 1;
    assert!(x << 0 == 1);
}

#[test]
fn hex() {
    let formatted = format!("{:x}", 255);
    assert_eq!(&*formatted, "ff");
}

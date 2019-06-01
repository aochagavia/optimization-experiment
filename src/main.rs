mod solver;

use std::fmt::Write;

use solver::Solver;

fn student_const(student: usize, round: usize, teacher: usize) -> String {
    format!("s{}_r{}_t{}", student, round, teacher)
}

fn main() {
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
    ];

    let teachers = vec![
        "Niko",
        "Jordi",
        "Daniël",
    ];

    let rounds = 3;

    let mut input = String::new();

    // Declare variables
    for student in 0..students.len() {
        for round in 0..rounds {
            for teacher in 0..teachers.len() {
                writeln!(input, "(declare-const {} Bool)", student_const(student, round, teacher));
            }
        }
    }

    // Constraint: for each round, each student has only one assigned teacher
    for student in 0..students.len() {
        for round in 0..rounds {
            write!(input, "(assert (= 1 (+ ");
            for teacher in 0..teachers.len() {
                write!(input, "(ite {} 1 0) ", student_const(student, round, teacher));
            }
            writeln!(input, ")))");
        }
    }

    // Constraint: every teacher must have taught every student at least once
    for teacher in 0..teachers.len() {
        for student in 0..students.len() {
            write!(input, "(assert (or ");
            for round in 0..rounds {
                write!(input, "{} ", student_const(student, round, teacher));
            }
            writeln!(input, "))");
        }
    }

    // Constraint: at a given round, a teacher cannot teach more than max_students
    let max_students = students.len() / rounds;
    for teacher in 0..teachers.len() {
        for round in 0..rounds {
            write!(input, "(assert (>= {} (+ ", max_students);
            for student in 0..students.len() {
                write!(input, "(ite {} 1 0) ", student_const(student, round, teacher));
            }
            writeln!(input, ")))");
        }
    }

    // Constraint: each person should meet every other person
    // for student in 0..student.len() {
    //
    // }

    // Fire up solver and check sat
    let mut solver = Solver::new();
    // println!("{}", input);
    solver.input(input);
    let sat = solver.check_sat();
    assert!(sat);

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
}

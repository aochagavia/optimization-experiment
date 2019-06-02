#![allow(dead_code)]

mod randomized;
mod z3;

use std::time::Instant;

// fn benchmark(students: usize, teachers: usize, rounds: usize, iterations: usize) {
//     let start = Instant::now();
//     // z3::solve(students, teachers, rounds, minimum_meetings).expect("Failed to obtain solution");
//     let solution = randomized::solve(students, teachers, rounds, iterations);
//     let solution_score = solution.score(students, teachers);
//     let teacher_score = solution.teacher_score(students, teachers);

//     println!("{} students, {} teachers, {} rounds. Finished in {} ms.", students, teachers, rounds, start.elapsed().as_millis());
//     println!("Solution score: {} (each student meets in average {} other students)", solution_score, solution_score as f64 / students as f64 - 1.0);
//     println!("Teacher score: {} (each teacher teaches in average {} different students)", teacher_score, teacher_score as f64 / teachers as f64)
// }

fn benchmark(students: usize, teachers: usize, rounds: usize) {
    let start = Instant::now();
    let mut solution = z3::solve(students, teachers, rounds).expect("Failed to obtain solution");
    // let solution = randomized::solve(students, teachers, rounds, iterations);
    // let solution_score = solution.score(students, teachers);
    // let teacher_score = solution.teacher_score(students, teachers);

    println!("{} students, {} teachers, {} rounds. Finished in {} ms.", students, teachers, rounds, start.elapsed().as_millis());
    solution.print(students, teachers, rounds);
    // println!("Solution score: {} (each student meets in average {} other students)", solution_score, solution_score as f64 / students as f64 - 1.0);
    // println!("Teacher score: {} (each teacher teaches in average {} different students)", teacher_score, teacher_score as f64 / teachers as f64)
}

fn main() {
    benchmark(6, 2, 2);
    benchmark(6, 3, 3);
    benchmark(7, 3, 3);
    // for students in 5..=10 {
    //     benchmark(students, 3, 3);
    // }
    // for students in 9..=20 {
    //     benchmark(students, 5, 5, None);
    // }
    // for students in 9..=20 {
    //     benchmark(students, 3, 5, None);
    // }
    // for students in 9..=25 {
    //     benchmark(students, 5, 5, None);
    // }

    // benchmark(16, 4, 4, 100_00);
    // benchmark(9, 3, 3, None);

    // for students in 9..=20 {
    //     benchmark(students, 3, 3, None);
    // }
    // for students in 9..=20 {
    //     benchmark(students, 5, 5, None);
    // }
    // for students in 9..=20 {
    //     benchmark(students, 3, 5, None);
    // }
    // for students in 9..=25 {
    //     benchmark(students, 5, 5, None);
    // }
}

fn user_friendly() {
    // let students = vec![
    //     "Adolfo",
    //     "Hubert",
    //     "Tim",
    //     "Paul",
    //     "Lodewijk",
    //     "Mansour",
    //     "Joost",
    //     "Tato",
    //     "Martijn",
    //     "Everard",
    //     "Matthijs",
    //     "Henrik",
    //     "Remy",
    //     "Eugen",
    //     "Fabian",
    //     "Sebastian",
    //     "Ben",
    // ];

    // let teachers = vec![
    //     "Niko",
    //     "Jordi",
    //     "Daniël",
    // ];

    // let rounds = 3;

    // let mut solution = z3::solve(students.len(), teachers.len(), rounds).expect("Failed to obtain solution");

    // // Retrieve variable values
    // for round in 0..rounds {
    //     println!("========");
    //     println!("Round {}", round);
    //     println!("========");
    //     for (teacher, teacher_name) in teachers.iter().enumerate() {
    //         print!("{}: ", teacher_name);
    //         for (student, student_name) in students.iter().enumerate() {
    //             let is_teacher_for_student: bool = solution.is_teacher_for_student(student, teacher, round);
    //             if is_teacher_for_student {
    //                 print!("{}, ", student_name);
    //             }
    //         }
    //         println!();
    //     }

    //     println!();
    // }

    // // Retrieve people met
    // println!("============");
    // println!("Students met");
    // println!("============");
    // for (student, _) in students.iter().enumerate() {
    //     let meetings = solution.students_met(student);
    //     println!("{}: {}", student, meetings);
    // }
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

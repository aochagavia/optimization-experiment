mod solution;
mod solver;
mod z3;

use std::time::Instant;

fn benchmark(students: usize, teachers: usize, rounds: usize) {
    let start = Instant::now();
    solver::solve(students, teachers, rounds).expect("Failed to obtain solution");

    println!("{} students, {} teachers, {} rounds. Finished in {} ms.", students, teachers, rounds, start.elapsed().as_millis());
}

fn main() {
    for students in 9..=20 {
        benchmark(students, 2, 6);
    }
}

#[allow(dead_code)]
fn user_friendly() {
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
        "Max",
    ];

    let teachers = vec![
        "Niko",
        "Jordi",
        "Daniël",
    ];

    let rounds = 4;

    let solution = solver::solve(students.len(), teachers.len(), rounds).expect("Failed to obtain solution");
    solution.print(&students, &teachers);
}

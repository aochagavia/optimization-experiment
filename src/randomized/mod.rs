use std::cmp;
use std::collections::BTreeSet;
use std::iter;

use rand::prelude::*;

pub struct Solution {
    rounds: Vec<u8>,
}

impl Solution {
    pub fn score(&self, students: usize, teachers: usize) -> usize {
        // Idea: hopefully, the meeting objective will indirectly favor settings where the teachers are well distributed

        let mut meetings = BTreeSet::new();
        for round in self.rounds.chunks_exact(students) {
            for class in class_slices(round, students, teachers) {
                for student in class {
                    for other_student in class {
                        let low = cmp::min(student, other_student);
                        let high = cmp::max(student, other_student);
                        meetings.insert((low, high));
                    }
                }
            }
        }

        meetings.len()
    }

    pub fn teacher_score(&self, students: usize, teachers: usize) -> usize {
        let mut taught_by = vec![BTreeSet::new(); teachers];
        for round in self.rounds.chunks_exact(students) {
            for (teacher, &class) in class_slices(&round, students, teachers).iter().enumerate() {
                for &student in class {
                    taught_by[teacher].insert(student);
                }
            }
        }

        taught_by.iter().map(|set| set.len()).sum()
    }
}

pub fn solve(students: usize, teachers: usize, rounds: usize, iterations: usize) -> Solution {
    iter::repeat_with(|| random_solution(students, rounds))
        .take(iterations)
        .max_by_key(|solution| solution.score(students, teachers))
        .unwrap()
}

pub fn random_solution(students: usize, total_rounds: usize) -> Solution {
    let mut rounds = Vec::new();

    // Push the student numbers for each round
    for _ in 0..total_rounds {
        rounds.extend(0..students as u8);
    }

    // Now shuffle them!
    let mut rng = rand::thread_rng();
    for round in rounds.chunks_exact_mut(students) {
        round.shuffle(&mut rng);
    }

    Solution { rounds }
}

fn class_slices(round: &[u8], students: usize, teachers: usize) -> Vec<&[u8]> {
    let min_students_per_teacher = students / teachers;
    let mut class_sizes = vec![min_students_per_teacher; teachers];
    for teacher in 0..(students % teachers) {
        class_sizes[teacher] += 1;
    }

    let mut class_slices = Vec::with_capacity(teachers);
    let mut class_start = 0;
    for class_size in class_sizes {
        let class_end_exclusive = class_start + class_size;
        class_slices.push(&round[class_start..class_end_exclusive]);
        class_start = class_end_exclusive;
    }

    class_slices
}

#[test]
fn test_class_slices() {
    let students = 15;
    let teachers = 4;

    let round: Vec<_> = (0..students as u8).collect();
    let slices = class_slices(&round, students, teachers);
    let expected: Vec<&[u8]> = vec![&[0, 1, 2, 3], &[4, 5, 6, 7], &[8, 9, 10, 11], &[12, 13, 14]];
    assert_eq!(
        expected,
        slices,
    );

    let students = 13;
    let teachers = 4;

    let round: Vec<_> = (0..students as u8).collect();
    let slices = class_slices(&round, students, teachers);
    let expected: Vec<&[u8]> = vec![&[0, 1, 2, 3], &[4, 5, 6], &[7, 8, 9], &[10, 11, 12]];
    assert_eq!(
        expected,
        slices,
    );

    let students = 12;
    let teachers = 4;

    let round: Vec<_> = (0..students as u8).collect();
    let slices = class_slices(&round, students, teachers);
    let expected: Vec<&[u8]> = vec![&[0, 1, 2], &[3, 4, 5], &[6, 7, 8], &[9, 10, 11]];
    assert_eq!(
        expected,
        slices,
    );
}

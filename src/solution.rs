use std::collections::HashSet;

use crate::solver::student_const;
use crate::z3::Z3;

pub struct Solution {
    students: usize,
    teachers: usize,
    rounds: usize,
    student_consts: HashSet<String>,
}

impl Solution {
    pub fn new(z3: &mut Z3, students: usize, teachers: usize, rounds: usize) -> Solution {
        let mut student_consts = HashSet::new();

        for round in 0..rounds {
            for teacher in 0..teachers {
                for student in 0..students {
                    if is_teacher_for_student(z3, student, teacher, round) {
                        student_consts.insert(student_const(student, round, teacher));
                    }
                }
            }
        }

        Solution { student_consts, students, teachers, rounds }
    }

    pub fn print<T: AsRef<str>>(&self, students: &[T], teachers: &[T]) {
        assert_eq!(students.len(), self.students);
        assert_eq!(teachers.len(), self.teachers);

        for round in 0..self.rounds {
            println!("Ronde {}", round + 1);
            for teacher in 0..self.teachers {
                print!("{}: ", teachers[teacher].as_ref());
                for student in 0..self.students {
                    if self.is_teacher_for_student(student, teacher, round) {
                        print!("{}, ", students[student].as_ref());
                    }
                }
                println!();
            }
        }
    }

    pub fn is_teacher_for_student(&self, student: usize, teacher: usize, round: usize) -> bool {
        self.student_consts.contains(&student_const(student, round, teacher))
    }
}

fn is_teacher_for_student(z3: &mut Z3, student: usize, teacher: usize, round: usize) -> bool {
    z3.eval(student_const(student, round, teacher)).parse().unwrap()
}

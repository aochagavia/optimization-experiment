use crate::z3::student_const;
use crate::z3::solver::Solver;

pub struct Solution {
    solver: Solver,
}

impl Solution {
    pub fn new(solver: Solver) -> Solution {
        Solution { solver }
    }

    pub fn is_teacher_for_student(&mut self, student: usize, teacher: usize, round: usize) -> bool {
        self.solver.eval(student_const(student, round, teacher)).parse().unwrap()
    }

    pub fn students_met(&mut self, student: usize) -> String {
        self.solver.eval(format!("s{}", student))
    }
}

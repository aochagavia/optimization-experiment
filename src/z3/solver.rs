use std::io::{BufReader, BufRead, Write};
use std::process::{ChildStdin, ChildStdout, Command, Stdio};

#[derive(Copy, Clone, Debug, PartialEq, Eq)]
pub enum Satisfiability {
    Sat,
    Unsat,
    Unknown,
}

#[derive(Debug)]
pub struct Solver {
    z3_stdin: ChildStdin,
    z3_stdout: BufReader<ChildStdout>,
}

impl Solver {
    pub fn new() -> Solver {
        let z3 = Command::new("z3")
            .args(&["-in"])
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .spawn()
            .expect("Failed to spawn Z3 process");

        Solver {
            z3_stdin: z3.stdin.expect("Failed to open stdin to Z3"),
            z3_stdout: BufReader::new(z3.stdout.expect("Failed to open stdout to Z3")),
        }
    }

    pub fn input(&mut self, input: &str) {
        writeln!(self.z3_stdin, "{}", input).expect("Failed to send input to Z3 process");
    }

    pub fn check_sat(&mut self) -> Satisfiability {
        writeln!(self.z3_stdin, "(check-sat)").expect("Failed to check_sat");
        let sat = self.read_line();
        match &*sat {
            "sat" => Satisfiability::Sat,
            "unsat" => Satisfiability::Unsat,
            "unknown" => Satisfiability::Unknown,
            _ => panic!("Unknown value for satisfiability: {}", sat), // FIXME: what about unknown and such?
        }
    }

    pub fn eval(&mut self, expr: String) -> String {
        writeln!(self.z3_stdin, "(eval {})", expr).expect("Failed to eval");
        self.read_line()
    }

    pub fn read_line(&mut self) -> String {
        let mut buf = String::new();
        self.z3_stdout.read_line(&mut buf).expect("Failed to read line from Z3 process");
        buf.trim().to_string()
    }
}

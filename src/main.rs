mod solution;
mod solver;
mod z3;

#[allow(dead_code)]
fn debug() {
    solver::solve(16, 2, 6).expect("Failed to obtain solution");
}

fn main() {
    std::panic::set_hook(Box::new(|e| {
        println!("Onverwachte fout: {}", e);
        wait_for_enter_and_exit_with_code(1);
    }));

    use std::io::{self, Write};

    let docenten = read_file_lines("docenten.txt");
    let studenten = read_file_lines("studenten.txt");

    println!("Docenten: ");
    for (i, docent) in docenten.iter().enumerate() {
        println!("{}. {}", i + 1, docent);
    }

    println!("Studenten: ");
    for (i, student) in studenten.iter().enumerate() {
        println!("{}. {}", i + 1, student);
    }

    print!("Voer aantal rondes in: ");
    io::stdout().flush().unwrap();

    let mut buf = String::new();
    io::stdin().read_line(&mut buf).unwrap();

    let rondes: usize = buf.trim()
        .parse()
        .unwrap_or_else(|_| {
            println!("Geen geldig getal ingevuld. Het programma kan niet doorgaan.");
            wait_for_enter_and_exit_with_code(1);
        });

    let solution = solver::solve(studenten.len(), docenten.len(), rondes).expect("Failed to obtain solution");
    solution.print(&studenten, &docenten);

    wait_for_enter_and_exit_with_code(0);
}

fn read_file_lines(filename: &str) -> Vec<String> {
    use std::fs::File;
    use std::io::{BufRead, BufReader};

    let f = File::open(filename).unwrap_or_else(|_| {
        println!("Het bestand {} kon niet geopend worden. Het programma kan niet doorgaan.", filename);
        wait_for_enter_and_exit_with_code(1);
    });

    BufReader::new(f)
        .lines()
        .map(|line| line.unwrap_or_else(|_| {
            println!("Het bestand {} kon niet worden ingeladen. Het programma kan niet doorgaan.", filename);
            wait_for_enter_and_exit_with_code(1);
        }))
        .filter(|s| s.trim() != "")
        .collect()
}

fn wait_for_enter_and_exit_with_code(code: i32) -> ! {
    println!("Druk op enter om te sluiten...");
    std::io::stdin().read_line(&mut String::new()).unwrap();
    std::process::exit(code)
}

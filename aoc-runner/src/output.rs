use colored::Colorize;

pub const NUMBER_DASHES: usize = 80;

pub fn print_header() {
    println!("{}", "-".repeat(NUMBER_DASHES).green().bold());
    println!(
        "{} {} {}",
        "-".repeat(NUMBER_DASHES / 2 - 10).red().bold(),
        "Advent of Code 2020".bold(),
        "-".repeat(NUMBER_DASHES / 2 - 11).red().bold()
    );
    println!("{}", "-".repeat(NUMBER_DASHES).green().bold());
}

pub fn print_day(day: usize) {
    println!("- {}", format!("Day {:02}", day).bold());
}

pub fn print_part(part: usize, output: &str, output_value: &str) {
    let part_string = if part == 1 {
        "Part 1".red().bold()
    } else {
        "Part 2".green().bold()
    };
    println!("    {}:", part_string);
    println!("      {}: {}", output, output_value);
}

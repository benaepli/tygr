use tygr::lexer::format::report_errors;
use tygr::lexer::LexError;

fn main() {
    let input = "let x = \"unterminated string";
    let errors = vec![LexError::UnterminatedString(8)];

    let _ = report_errors(input, &errors, "input.txt");
}

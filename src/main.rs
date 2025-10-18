use tygr::compiler::compile;

fn main() {
    let input2 = "let x = fix(fn 2 => if x == 0 then x + 5 else 2) let y = print(x)";
    let _ = compile(input2, "input2.txt");
}

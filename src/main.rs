use tygr::compiler::compile;

fn main() {
    let input2 = "let x = fix(fn x => if x == 0 then x + 5 else 2) let y = print(\"hi\")";
    let _ = compile(input2, "input2.txt");
}

use tygr::compiler::compile;

fn main() -> Result<(), anyhow::Error> {
    let input2 = "let x = fix(fn x => if x == 0 then x + 5 else 2) let y = print(x)";
    compile(input2, "input2.txt")
}

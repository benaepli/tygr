use tygr::compiler::compile;

fn main() -> Result<(), anyhow::Error>{
    let input2 = "let x = fn x => x + 5";
    compile(input2, "input2.txt")
}

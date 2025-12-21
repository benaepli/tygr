use crate::analysis::inference::{Typed, TypedKind, TypedPattern, TypedPatternKind};
use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::{Name, TypeName};
use crate::builtin::BuiltinFn;
use crate::parser::BinOp;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::rc::Rc;

#[derive(Clone)]
pub enum Value {
    Unit,
    Int(i64),
    Float(f64),
    Bool(bool),
    String(Rc<String>),
    List(Vec<Rc<Value>>),
    Pair(Rc<Value>, Rc<Value>),
    /// A standard first-class function, capturing its environment upon creation.
    Closure {
        param: TypedPattern,
        body: Box<Typed>,
        env: Environment,
    },
    /// A recursive function value created by a `Fix` expression. It captures the
    /// generator expression `f` from `fix(f)`.
    RecursiveClosure {
        generator_expr: Box<Typed>,
        captured_env: Environment,
    },
    /// A partially-applied built-in function, collecting arguments.
    PartialBuiltin {
        func: BuiltinFn,
        args: Vec<Rc<Value>>,
    },
    /// A built-in function implemented in Rust.
    Builtin(BuiltinFn),
    Record(HashMap<String, Value>),
    Constructor(TypeName, Name),
    Variant(Rc<Value>, TypeName, Name),
}

impl fmt::Debug for Value {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Value::Unit => write!(f, "()"),
            Value::Int(i) => write!(f, "{}", i),
            Value::Float(fl) => write!(f, "{}", fl),
            Value::Bool(b) => write!(f, "{}", b),
            Value::String(s) => write!(f, "\"{}\"", s),
            Value::List(v) => f.debug_list().entries(v.iter()).finish(),
            Value::Pair(a, b) => f.debug_tuple("Pair").field(a).field(b).finish(),
            Value::Closure { .. } => write!(f, "<closure>"),
            Value::RecursiveClosure { .. } => write!(f, "<recursive_closure>"),
            Value::PartialBuiltin { func, args } => f
                .debug_struct("PartialBuiltin")
                .field("func", func)
                .field("args", args)
                .finish(),
            Value::Builtin(b) => f.debug_tuple("Builtin").field(b).finish(),
            Value::Record(fields) => {
                let mut debug_map = f.debug_map();
                for (name, value) in fields {
                    debug_map.entry(&name, value);
                }
                debug_map.finish()
            }
            Value::Constructor(_def_id, name) => write!(f, "<constructor:{}>", name),
            Value::Variant(val, _def_id, name) => f
                .debug_tuple(&format!("Variant::{}", name))
                .field(val)
                .finish(),
        }
    }
}

pub struct ValueDisplay<'a> {
    pub value: &'a Value,
    pub name_table: &'a NameTable,
}

impl<'a> ValueDisplay<'a> {
    pub fn new(value: &'a Value, name_table: &'a NameTable) -> Self {
        Self { value, name_table }
    }
}

impl<'a> fmt::Display for ValueDisplay<'a> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.value {
            Value::Unit => write!(f, "()"),
            Value::Int(i) => write!(f, "{}", i),
            Value::Float(fl) => write!(f, "{}", fl),
            Value::Bool(b) => write!(f, "{}", b),
            Value::String(s) => write!(f, "{}", s),
            Value::List(v) => {
                f.write_str("[")?;
                for (i, val) in v.iter().enumerate() {
                    if i > 0 {
                        f.write_str(", ")?;
                    }
                    write!(f, "{}", ValueDisplay::new(val, self.name_table))?;
                }
                f.write_str("]")
            }
            Value::Pair(a, b) => write!(
                f,
                "({}, {})",
                ValueDisplay::new(a, self.name_table),
                ValueDisplay::new(b, self.name_table)
            ),
            Value::Closure { .. } => write!(f, "<closure>"),
            Value::RecursiveClosure { .. } => write!(f, "<recursive_closure>"),
            Value::PartialBuiltin { .. } => write!(f, "<partial_builtin>"),
            Value::Builtin(_) => write!(f, "<builtin>"),
            Value::Record(fields) => {
                write!(f, "{{ ")?;
                let mut first = true;
                for (name, value) in fields {
                    if !first {
                        write!(f, ", ")?;
                    }
                    write!(f, "{}: {}", name, ValueDisplay::new(value, self.name_table))?;
                    first = false;
                }
                write!(f, " }}")
            }
            Value::Constructor(_def_id, name) => {
                write!(f, "<{}>", self.name_table.lookup_name(name))
            }
            Value::Variant(val, _def_id, name) => {
                let ctor_name = self.name_table.lookup_name(name);
                if let Value::Unit = **val {
                    write!(f, "{}", ctor_name)
                } else {
                    write!(
                        f,
                        "{}({})",
                        ctor_name,
                        ValueDisplay::new(val, self.name_table)
                    )
                }
            }
        }
    }
}

/// Represents an error that can occur during evaluation.
#[derive(Debug, Clone)]
pub enum EvalError {
    UndefinedVariable(Name),
    PatternMismatch(String),
    TypeMismatch(String),
    NotAFunction,
    NonExhaustiveMatch,
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::UndefinedVariable(name) => write!(f, "Undefined variable: {}", name),
            EvalError::PatternMismatch(msg) => write!(f, "Pattern match failed: {}", msg),
            EvalError::TypeMismatch(msg) => write!(f, "Type mismatch: {}", msg),
            EvalError::NotAFunction => write!(f, "Attempted to call a non-function value"),
            EvalError::NonExhaustiveMatch => write!(f, "Non-exhaustive match"),
        }
    }
}

pub type EvalResult = Result<Rc<Value>, EvalError>;

/// The execution environment, mapping names to values.
#[derive(Debug, Clone)]
pub struct Environment {
    bindings: HashMap<Name, Rc<RefCell<Rc<Value>>>>,
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            bindings: HashMap::new(),
        }
    }

    pub fn get(&self, name: &Name) -> Option<Rc<Value>> {
        self.bindings.get(name).map(|cell| cell.borrow().clone())
    }

    pub fn insert_cell(&mut self, name: Name, cell: Rc<RefCell<Rc<Value>>>) {
        self.bindings.insert(name, cell);
    }

    pub fn insert(&mut self, name: Name, value: Rc<Value>) {
        self.bindings.insert(name, Rc::new(RefCell::new(value)));
    }
}

fn bind_pattern(
    pattern: &TypedPattern,
    value: Rc<Value>,
    env: &mut Environment,
) -> Result<(), EvalError> {
    match &pattern.kind {
        TypedPatternKind::Var { name } => {
            env.insert(*name, value);
            Ok(())
        }
        TypedPatternKind::Wildcard => Ok(()),
        TypedPatternKind::Unit => {
            if let Value::Unit = &*value {
                Ok(())
            } else {
                Err(EvalError::PatternMismatch(format!(
                    "expected unit, found {:?}",
                    value
                )))
            }
        }
        TypedPatternKind::Pair(p1, p2) => {
            if let Value::Pair(v1, v2) = &*value {
                bind_pattern(p1, v1.clone(), env)?;
                bind_pattern(p2, v2.clone(), env)
            } else {
                Err(EvalError::PatternMismatch(format!(
                    "expected pair, found {:?}",
                    value
                )))
            }
        }
        TypedPatternKind::EmptyList => {
            if let Value::List(v) = &*value {
                if v.is_empty() {
                    Ok(())
                } else {
                    Err(EvalError::PatternMismatch(format!(
                        "expected empty list, found {:?}",
                        value
                    )))
                }
            } else {
                Err(EvalError::PatternMismatch(format!(
                    "expected list, found {:?}",
                    value
                )))
            }
        }
        TypedPatternKind::Cons(p1, p2) => {
            if let Value::List(v) = &*value {
                if !v.is_empty() {
                    bind_pattern(p1, v[0].clone(), env)?;

                    let remainder = v[1..].to_vec();
                    bind_pattern(p2, Rc::new(Value::List(remainder)), env)
                } else {
                    Err(EvalError::PatternMismatch(format!(
                        "got empty list {:?}",
                        value
                    )))
                }
            } else {
                Err(EvalError::PatternMismatch(format!(
                    "expected list, found {:?}",
                    value
                )))
            }
        }
        TypedPatternKind::Record(fields) => {
            if let Value::Record(values) = &*value {
                for (name, pat) in fields {
                    match values.get(name) {
                        Some(val) => {
                            bind_pattern(pat, Rc::new(val.clone()), env)?;
                        }
                        None => {
                            return Err(EvalError::PatternMismatch(format!(
                                "field '{}' not found in record",
                                name
                            )));
                        }
                    }
                }
                Ok(())
            } else {
                Err(EvalError::PatternMismatch(format!(
                    "expected record, found {:?}",
                    value
                )))
            }
        }
        TypedPatternKind::Constructor(variant_id, ctor_id, pat) => {
            if let Value::Variant(v, variant, ctor) = &*value
                && variant == variant_id
            {
                if ctor == ctor_id {
                    bind_pattern(pat, v.clone(), env)
                } else {
                    Err(EvalError::PatternMismatch(format!(
                        "expected constructor {}, found constructor {}",
                        ctor_id, ctor
                    )))
                }
            } else {
                Err(EvalError::PatternMismatch(format!(
                    "expected variant constructor pattern, found {:?}",
                    value
                )))
            }
        }
    }
}
fn eval_binop(op: BinOp, lhs: Rc<Value>, rhs: Rc<Value>) -> EvalResult {
    match op {
        BinOp::And | BinOp::Or => {
            let l = match *lhs {
                Value::Bool(b) => b,
                _ => {
                    return Err(EvalError::TypeMismatch(
                        "expected boolean for logical operator".into(),
                    ));
                }
            };
            let r = match *rhs {
                Value::Bool(b) => b,
                _ => {
                    return Err(EvalError::TypeMismatch(
                        "expected boolean for logical operator".into(),
                    ));
                }
            };
            Ok(Rc::new(Value::Bool(match op {
                BinOp::And => l && r,
                BinOp::Or => l || r,
            })))
        }
    }
}

fn builtin_arity(builtin: &BuiltinFn) -> usize {
    use BuiltinFn::*;
    match builtin {
        // Unary functions
        IntNegate | FloatNegate | Not | Print | StringOfFloat | StringOfInt | FloatOfInt
        | Floor | Ceil | TimeMicro => 1,

        // Binary functions
        IntAdd | IntSubtract | IntMultiply | IntDivide | FloatAdd | FloatSubtract
        | FloatMultiply | FloatDivide | IntEqual | IntNotEqual | IntLessEqual | IntGreaterEqual
        | IntLess | IntGreater | FloatEqual | FloatNotEqual | FloatLessEqual
        | FloatGreaterEqual | FloatLess | FloatGreater | BoolEqual | BoolNotEqual
        | StringConcat => 2,
    }
}

fn eval_builtin(op: BuiltinFn, args: &[Rc<Value>]) -> EvalResult {
    use BuiltinFn::*;
    // Helper macro to reduce boilerplate for extracting typed values.
    macro_rules! as_int {
        ($val:expr) => {
            if let Value::Int(i) = **$val {
                i
            } else {
                return Err(EvalError::TypeMismatch(format!(
                    "Expected Int, found {:?}",
                    $val
                )));
            }
        };
    }
    macro_rules! as_float {
        ($val:expr) => {
            if let Value::Float(f) = **$val {
                f
            } else {
                return Err(EvalError::TypeMismatch(format!(
                    "Expected Float, found {:?}",
                    $val
                )));
            }
        };
    }
    macro_rules! as_bool {
        ($val:expr) => {
            if let Value::Bool(b) = **$val {
                b
            } else {
                return Err(EvalError::TypeMismatch(format!(
                    "Expected Bool, found {:?}",
                    $val
                )));
            }
        };
    }
    macro_rules! as_string {
        ($val:expr) => {
            if let Value::String(s) = &**$val {
                s.clone()
            } else {
                return Err(EvalError::TypeMismatch(format!(
                    "Expected String, found {:?}",
                    $val
                )));
            }
        };
    }

    match op {
        IntAdd | IntSubtract | IntMultiply | IntDivide => {
            let l = as_int!(&args[0]);
            let r = as_int!(&args[1]);
            // Note: Division by zero will panic. A robust interpreter would handle this.
            let result = match op {
                IntAdd => l + r,
                IntSubtract => l - r,
                IntMultiply => l * r,
                IntDivide => l / r,
                _ => unreachable!(),
            };
            Ok(Rc::new(Value::Int(result)))
        }

        FloatAdd | FloatSubtract | FloatMultiply | FloatDivide => {
            let l = as_float!(&args[0]);
            let r = as_float!(&args[1]);
            let result = match op {
                FloatAdd => l + r,
                FloatSubtract => l - r,
                FloatMultiply => l * r,
                FloatDivide => l / r,
                _ => unreachable!(),
            };
            Ok(Rc::new(Value::Float(result)))
        }

        IntEqual | IntNotEqual | IntLessEqual | IntGreaterEqual | IntLess | IntGreater => {
            let l = as_int!(&args[0]);
            let r = as_int!(&args[1]);
            let result = match op {
                IntEqual => l == r,
                IntNotEqual => l != r,
                IntLessEqual => l <= r,
                IntGreaterEqual => l >= r,
                IntLess => l < r,
                IntGreater => l > r,
                _ => unreachable!(),
            };
            Ok(Rc::new(Value::Bool(result)))
        }

        FloatEqual | FloatNotEqual | FloatLessEqual | FloatGreaterEqual | FloatLess
        | FloatGreater => {
            let l = as_float!(&args[0]);
            let r = as_float!(&args[1]);
            let result = match op {
                FloatEqual => l == r,
                FloatNotEqual => l != r,
                FloatLessEqual => l <= r,
                FloatGreaterEqual => l >= r,
                FloatLess => l < r,
                FloatGreater => l > r,
                _ => unreachable!(),
            };
            Ok(Rc::new(Value::Bool(result)))
        }

        BoolEqual | BoolNotEqual => {
            let l = as_bool!(&args[0]);
            let r = as_bool!(&args[1]);
            let result = match op {
                BoolEqual => l == r,
                BoolNotEqual => l != r,
                _ => unreachable!(),
            };
            Ok(Rc::new(Value::Bool(result)))
        }

        IntNegate => Ok(Rc::new(Value::Int(-as_int!(&args[0])))),
        FloatNegate => Ok(Rc::new(Value::Float(-as_float!(&args[0])))),
        Not => Ok(Rc::new(Value::Bool(!as_bool!(&args[0])))),

        StringConcat => {
            let s1 = as_string!(&args[0]);
            let s2 = as_string!(&args[1]);
            Ok(Rc::new(Value::String(Rc::new(format!("{}{}", s1, s2)))))
        }

        Print => {
            let s = as_string!(&args[0]);
            println!("{}", s);
            Ok(Rc::new(Value::String(s)))
        }
        StringOfFloat => Ok(Rc::new(Value::String(Rc::new(
            as_float!(&args[0]).to_string(),
        )))),
        StringOfInt => Ok(Rc::new(Value::String(Rc::new(
            as_int!(&args[0]).to_string(),
        )))),
        FloatOfInt => Ok(Rc::new(Value::Float(as_int!(&args[0]) as f64))),
        Floor => Ok(Rc::new(Value::Int(as_float!(&args[0]).floor() as i64))),
        Ceil => Ok(Rc::new(Value::Int(as_float!(&args[0]).ceil() as i64))),
        TimeMicro => {
            use std::time::{SystemTime, UNIX_EPOCH};
            let start = SystemTime::now();
            let since_the_epoch = start
                .duration_since(UNIX_EPOCH)
                .expect("Time went backwards");
            Ok(Rc::new(Value::Int(since_the_epoch.as_micros() as i64)))
        }
    }
}

fn apply(func: Rc<Value>, arg: Rc<Value>) -> EvalResult {
    match &*func {
        Value::Closure {
            param,
            body,
            env: captured_env,
        } => {
            let mut new_env = captured_env.clone();
            bind_pattern(param, arg, &mut new_env)?;
            eval(body, &mut new_env)
        }
        Value::RecursiveClosure {
            generator_expr,
            captured_env,
        } => {
            // A recursive closure `fix(f)` applied to an argument `x`
            // behaves like `(f (fix f)) x`.
            let generator_val = eval(generator_expr, &mut captured_env.clone())?;
            let actual_func = apply(generator_val, func.clone())?;
            apply(actual_func, arg)
        }
        Value::Builtin(b) => {
            let arity = builtin_arity(b);
            if arity == 1 {
                eval_builtin(b.clone(), &[arg])
            } else {
                Ok(Rc::new(Value::PartialBuiltin {
                    func: b.clone(),
                    args: vec![arg],
                }))
            }
        }
        Value::PartialBuiltin { func, args } => {
            let arity = builtin_arity(func);
            let mut new_args = args.clone();
            new_args.push(arg);

            if new_args.len() == arity {
                eval_builtin(func.clone(), &new_args)
            } else {
                Ok(Rc::new(Value::PartialBuiltin {
                    func: func.clone(),
                    args: new_args,
                }))
            }
        }
        Value::Constructor(variant_id, ctor_id) => Ok(Rc::new(Value::Variant(
            arg,
            variant_id.clone(),
            ctor_id.clone(),
        ))),
        _ => Err(EvalError::NotAFunction),
    }
}

fn eval(expr: &Typed, env: &mut Environment) -> EvalResult {
    match &expr.kind {
        TypedKind::Var(name) => env
            .get(name)
            .ok_or_else(|| EvalError::UndefinedVariable(*name)),
        TypedKind::IntLit(i) => Ok(Rc::new(Value::Int(*i))),
        TypedKind::FloatLit(f) => Ok(Rc::new(Value::Float(*f))),
        TypedKind::BoolLit(b) => Ok(Rc::new(Value::Bool(*b))),
        TypedKind::StringLit(s) => Ok(Rc::new(Value::String(Rc::new(s.clone())))),
        TypedKind::UnitLit => Ok(Rc::new(Value::Unit)),
        TypedKind::PairLit(e1, e2) => {
            let v1 = eval(e1, env)?;
            let v2 = eval(e2, env)?;
            Ok(Rc::new(Value::Pair(v1, v2)))
        }
        TypedKind::Lambda { param, body, .. } => Ok(Rc::new(Value::Closure {
            param: param.clone(),
            body: body.clone(),
            env: env.clone(),
        })),
        TypedKind::Let { name, value, body } => {
            let val = eval(value, env)?;
            let mut new_env = env.clone();
            bind_pattern(name, val, &mut new_env)?;
            eval(body, &mut new_env)
        }
        TypedKind::If(cond, then_branch, else_branch) => {
            let cond_val = eval(cond, env)?;
            match &*cond_val {
                Value::Bool(b) => {
                    if *b {
                        eval(then_branch, env)
                    } else {
                        eval(else_branch, env)
                    }
                }
                _ => Err(EvalError::TypeMismatch(
                    "If condition must be a boolean".into(),
                )),
            }
        }
        TypedKind::Match(expr, branches) => {
            let val = eval(expr, env)?;
            let mut new_env = env.clone();
            for branch in branches {
                let result = bind_pattern(&branch.pattern, val.clone(), &mut new_env);
                if result.is_err() {
                    continue;
                }
                return eval(&*branch.expr, &mut new_env);
            }
            Err(EvalError::NonExhaustiveMatch)
        }
        TypedKind::App(func_expr, arg_expr) => {
            let func_val = eval(func_expr, env)?;
            let arg_val = eval(arg_expr, env)?;
            apply(func_val, arg_val)
        }
        TypedKind::Fix(generator_expr) => {
            // The value of `fix(f)` is a special `RecursiveClosure` value.
            // It captures the expression `f` and the current environment.
            Ok(Rc::new(Value::RecursiveClosure {
                generator_expr: generator_expr.clone(),
                captured_env: env.clone(),
            }))
        }
        TypedKind::BinOp(op, lhs, rhs) => {
            let left = eval(lhs, env)?;
            let right = eval(rhs, env)?;
            eval_binop(op.clone(), left, right)
        }
        TypedKind::Builtin(b) => Ok(Rc::new(Value::Builtin(b.clone()))),
        TypedKind::EmptyListLit => Ok(Rc::new(Value::List(vec![]))),
        TypedKind::Cons(e1, e2) => {
            let v1 = eval(e1, env)?;
            let v2 = eval(e2, env)?;
            match &*v2 {
                Value::List(list) => {
                    let new_list = vec![v1];
                    let combined = new_list.iter().chain(list.iter()).cloned().collect();
                    Ok(Rc::new(Value::List(combined)))
                }
                _ => Err(EvalError::TypeMismatch(
                    "Cons second argument must be a list".into(),
                )),
            }
        }
        TypedKind::RecordLit(fields) => {
            let mut record_fields = HashMap::new();
            for (name, expr) in fields {
                let value = eval(expr, env)?;
                record_fields.insert(name.clone(), (*value).clone());
            }
            Ok(Rc::new(Value::Record(record_fields)))
        }
        TypedKind::FieldAccess(record_expr, field_name) => {
            let record_val = eval(record_expr, env)?;
            match &*record_val {
                Value::Record(fields) => fields
                    .get(field_name)
                    .map(|v| Rc::new(v.clone()))
                    .ok_or_else(|| {
                        EvalError::TypeMismatch(format!("Field {} not found in record", field_name))
                    }),
                _ => Err(EvalError::TypeMismatch(format!(
                    "Expected record for field access, found {:?}",
                    record_val
                ))),
            }
        }
        &TypedKind::Constructor(variant_id, ctor_id) => {
            Ok(Rc::new(Value::Constructor(variant_id, ctor_id)))
        }

        TypedKind::RecRecord(fields) => {
            let mut placeholders = Vec::new();
            let mut rec_env = env.clone();

            // Placeholders
            for (_label, (name_id, _expr)) in fields.iter() {
                let placeholder = Rc::new(RefCell::new(Rc::new(Value::Unit)));
                rec_env.insert_cell(*name_id, placeholder.clone());
                placeholders.push((*name_id, placeholder));
            }

            // Evaluate in the new environment where names point to placeholders.
            let mut evaluated_results = Vec::new();
            for (label, (name_id, expr)) in fields {
                let val = eval(expr, &mut rec_env)?;
                evaluated_results.push((label, name_id, val));
            }

            // Update the RefCells with the actual evaluated values.
            let mut record_map = HashMap::new();
            for (label, name_id, actual_val) in evaluated_results {
                let placeholder_cell = rec_env.bindings.get(&name_id).unwrap();
                *placeholder_cell.borrow_mut() = actual_val.clone();

                record_map.insert(label.clone(), (*actual_val).clone());
            }

            Ok(Rc::new(Value::Record(record_map)))
        }
    }
}

/// Main entry point for the interpreter.
/// Creates an initial empty environment and starts evaluation.
pub fn run(expr: &Typed) -> EvalResult {
    let mut initial_env = Environment::new();
    eval(expr, &mut initial_env)
}

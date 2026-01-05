use crate::analysis::inference::{
    Typed, TypedGroup, TypedKind, TypedPattern, TypedPatternKind, TypedStatement,
};
use crate::analysis::name_table::NameTable;
use crate::analysis::resolver::{GlobalName, GlobalType};
use crate::builtin::BuiltinFn;
use crate::custom::{CustomFnId, CustomFnRegistry};
use crate::parser::BinOp;
use std::cell::RefCell;
use std::collections::HashMap;
use std::fmt;
use std::io::Write;
use std::rc::Rc;

#[derive(Clone, serde::Serialize, serde::Deserialize)]
#[serde(tag = "type", content = "value")]
pub enum Value {
    Unit,
    Int(i64),
    Float(f64),
    Bool(bool),
    String(Rc<String>),
    List(Vec<Rc<Value>>),
    Pair(Rc<Value>, Rc<Value>),
    /// A standard first-class function, capturing its environment upon creation.
    #[serde(skip)]
    Closure {
        param: TypedPattern,
        body: Box<Typed>,
        env: Environment,
    },
    /// A partially-applied built-in function, collecting arguments.
    #[serde(skip)]
    PartialBuiltin {
        func: BuiltinFn,
        args: Vec<Rc<Value>>,
    },
    /// A built-in function implemented in Rust.
    #[serde(skip)]
    Builtin(BuiltinFn),
    Record(HashMap<String, Value>),
    #[serde(skip)]
    Constructor(GlobalType, GlobalName),
    #[serde(skip)]
    Variant(Rc<Value>, GlobalType, GlobalName),
    /// A custom function implemented via the CustomFn trait.
    #[serde(skip)]
    Custom(CustomFnId),
    /// A partially-applied custom function, collecting arguments.
    #[serde(skip)]
    PartialCustom {
        id: CustomFnId,
        args: Vec<Rc<Value>>,
    },
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
            Value::Constructor(_def_id, name) => {
                write!(f, "<constructor:{:?}\\{}>", name.krate, name.name)
            }
            Value::Variant(val, _def_id, name) => f
                .debug_tuple(&format!("Variant::{}", name))
                .field(val)
                .finish(),
            Value::Custom(id) => write!(f, "<custom:{}>", id),
            Value::PartialCustom { id, args } => f
                .debug_struct("PartialCustom")
                .field("id", id)
                .field("args", args)
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
            Value::PartialBuiltin { .. } => write!(f, "<partial_builtin>"),
            Value::Builtin(_) => write!(f, "<builtin>"),
            Value::Custom(_) => write!(f, "<custom>"),
            Value::PartialCustom { .. } => write!(f, "<partial_custom>"),
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
    UndefinedVariable(GlobalName),
    PatternMismatch(String),
    TypeMismatch(String),
    NotAFunction,
    NonExhaustiveMatch,
    CustomFunctionNotFound(CustomFnId),
    IOError(String),
}

impl fmt::Display for EvalError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            EvalError::UndefinedVariable(name) => write!(f, "Undefined variable: {}", name),
            EvalError::PatternMismatch(msg) => write!(f, "Pattern match failed: {}", msg),
            EvalError::TypeMismatch(msg) => write!(f, "Type mismatch: {}", msg),
            EvalError::NotAFunction => write!(f, "Attempted to call a non-function value"),
            EvalError::NonExhaustiveMatch => write!(f, "Non-exhaustive match"),
            EvalError::CustomFunctionNotFound(id) => write!(f, "Custom function {} not found", id),
            EvalError::IOError(msg) => write!(f, "IO error: {}", msg),
        }
    }
}

pub type EvalResult = Result<Rc<Value>, EvalError>;

/// The execution environment, mapping names to values.
#[derive(Clone)]
pub struct Environment {
    bindings: HashMap<GlobalName, Rc<RefCell<Rc<Value>>>>,
    pub output: Rc<RefCell<dyn Write>>,
}

impl Default for Environment {
    fn default() -> Self {
        Self::new()
    }
}

impl fmt::Debug for Environment {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Environment")
            .field("bindings", &self.bindings)
            .finish_non_exhaustive()
    }
}

impl Environment {
    pub fn new() -> Self {
        Environment {
            bindings: HashMap::new(),
            output: Rc::new(RefCell::new(std::io::stdout())),
        }
    }

    pub fn with_output(output: Rc<RefCell<dyn Write>>) -> Self {
        Environment {
            bindings: HashMap::new(),
            output,
        }
    }

    pub fn get(&self, name: &GlobalName) -> Option<Rc<Value>> {
        self.bindings.get(name).map(|cell| cell.borrow().clone())
    }

    pub fn insert_cell(&mut self, name: GlobalName, cell: Rc<RefCell<Rc<Value>>>) {
        self.bindings.insert(name, cell);
    }

    pub fn insert(&mut self, name: GlobalName, value: Rc<Value>) {
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
                    match pat {
                        Some(p) => bind_pattern(p, v.clone(), env),
                        None => Ok(()), // Nullary constructor, nothing to bind
                    }
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

fn eval_builtin(op: BuiltinFn, args: &[Rc<Value>], env: &mut Environment) -> EvalResult {
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
            let mut out = env.output.borrow_mut();
            writeln!(out, "{}", s)
                .map_err(|e| EvalError::IOError(format!("Failed to write to output: {}", e)))?;
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

fn apply(
    func: Rc<Value>,
    arg: Rc<Value>,
    env: &mut Environment,
    custom_fns: &CustomFnRegistry,
) -> EvalResult {
    match &*func {
        Value::Closure {
            param,
            body,
            env: captured_env,
        } => {
            let mut new_env = captured_env.clone();
            bind_pattern(param, arg, &mut new_env)?;
            eval(body, &mut new_env, custom_fns)
        }
        Value::Builtin(b) => {
            let arity = builtin_arity(b);
            if arity == 1 {
                eval_builtin(b.clone(), &[arg], env)
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
                eval_builtin(func.clone(), &new_args, env)
            } else {
                Ok(Rc::new(Value::PartialBuiltin {
                    func: func.clone(),
                    args: new_args,
                }))
            }
        }
        Value::Custom(id) => {
            let custom_fn = custom_fns
                .get(*id)
                .ok_or(EvalError::CustomFunctionNotFound(*id))?;
            let arity = custom_fn.arity();
            if arity == 1 {
                custom_fn.call(&[arg], env)
            } else {
                Ok(Rc::new(Value::PartialCustom {
                    id: *id,
                    args: vec![arg],
                }))
            }
        }
        Value::PartialCustom { id, args } => {
            let custom_fn = custom_fns
                .get(*id)
                .ok_or(EvalError::CustomFunctionNotFound(*id))?;
            let arity = custom_fn.arity();
            let mut new_args = args.clone();
            new_args.push(arg);

            if new_args.len() == arity {
                custom_fn.call(&new_args, env)
            } else {
                Ok(Rc::new(Value::PartialCustom {
                    id: *id,
                    args: new_args,
                }))
            }
        }
        Value::Constructor(variant_id, ctor_id) => {
            Ok(Rc::new(Value::Variant(arg, *variant_id, *ctor_id)))
        }
        _ => Err(EvalError::NotAFunction),
    }
}

fn eval(expr: &Typed, env: &mut Environment, custom_fns: &CustomFnRegistry) -> EvalResult {
    match &expr.kind {
        TypedKind::Var(name) => env.get(name).ok_or(EvalError::UndefinedVariable(*name)),
        TypedKind::IntLit(i) => Ok(Rc::new(Value::Int(*i))),
        TypedKind::FloatLit(f) => Ok(Rc::new(Value::Float(*f))),
        TypedKind::BoolLit(b) => Ok(Rc::new(Value::Bool(*b))),
        TypedKind::StringLit(s) => Ok(Rc::new(Value::String(Rc::new(s.clone())))),
        TypedKind::UnitLit => Ok(Rc::new(Value::Unit)),
        TypedKind::PairLit(e1, e2) => {
            let v1 = eval(e1, env, custom_fns)?;
            let v2 = eval(e2, env, custom_fns)?;
            Ok(Rc::new(Value::Pair(v1, v2)))
        }
        TypedKind::Lambda { param, body, .. } => Ok(Rc::new(Value::Closure {
            param: param.clone(),
            body: body.clone(),
            env: env.clone(),
        })),
        TypedKind::If(cond, then_branch, else_branch) => {
            let cond_val = eval(cond, env, custom_fns)?;
            match &*cond_val {
                Value::Bool(b) => {
                    if *b {
                        eval(then_branch, env, custom_fns)
                    } else {
                        eval(else_branch, env, custom_fns)
                    }
                }
                _ => Err(EvalError::TypeMismatch(
                    "If condition must be a boolean".into(),
                )),
            }
        }
        TypedKind::Match(expr, branches) => {
            let val = eval(expr, env, custom_fns)?;
            for branch in branches {
                let mut new_env = env.clone();
                let result = bind_pattern(&branch.pattern, val.clone(), &mut new_env);
                if result.is_err() {
                    continue;
                }
                return eval(&branch.expr, &mut new_env, custom_fns);
            }
            Err(EvalError::NonExhaustiveMatch)
        }
        TypedKind::App(func_expr, arg_expr) => {
            let func_val = eval(func_expr, env, custom_fns)?;
            let arg_val = eval(arg_expr, env, custom_fns)?;
            apply(func_val, arg_val, env, custom_fns)
        }
        TypedKind::BinOp(op, lhs, rhs) => {
            let left = eval(lhs, env, custom_fns)?;
            let right = eval(rhs, env, custom_fns)?;
            eval_binop(op.clone(), left, right)
        }
        TypedKind::Builtin(b) => Ok(Rc::new(Value::Builtin(b.clone()))),
        TypedKind::EmptyListLit => Ok(Rc::new(Value::List(vec![]))),
        TypedKind::Cons(e1, e2) => {
            let v1 = eval(e1, env, custom_fns)?;
            let v2 = eval(e2, env, custom_fns)?;
            match &*v2 {
                Value::List(list) => {
                    let mut combined = Vec::with_capacity(list.len() + 1);
                    combined.push(v1);
                    combined.extend_from_slice(list);
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
                let value = eval(expr, env, custom_fns)?;
                record_fields.insert(name.clone(), (*value).clone());
            }
            Ok(Rc::new(Value::Record(record_fields)))
        }
        TypedKind::FieldAccess(record_expr, field_name) => {
            let record_val = eval(record_expr, env, custom_fns)?;
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
        TypedKind::Constructor {
            variant,
            ctor,
            nullary,
        } => {
            if *nullary {
                Ok(Rc::new(Value::Variant(
                    Rc::new(Value::Unit),
                    *variant,
                    *ctor,
                )))
            } else {
                Ok(Rc::new(Value::Constructor(*variant, *ctor)))
            }
        }

        TypedKind::RecRecord(fields) => {
            let mut rec_env = env.clone();
            for (_label, (name_id, _expr)) in fields.iter() {
                let placeholder = Rc::new(RefCell::new(Rc::new(Value::Unit)));
                rec_env.insert_cell(*name_id, placeholder.clone());
            }

            // Evaluate in the new environment where names point to placeholders.
            let mut evaluated_results = Vec::new();
            for (label, (name_id, expr)) in fields {
                let val = eval(expr, &mut rec_env, custom_fns)?;
                evaluated_results.push((label, name_id, val));
            }

            // Update the RefCells with the actual evaluated values.
            let mut record_map = HashMap::new();
            for (label, name_id, actual_val) in evaluated_results {
                let placeholder_cell = rec_env.bindings.get(name_id).unwrap();
                *placeholder_cell.borrow_mut() = actual_val.clone();

                record_map.insert(label.clone(), (*actual_val).clone());
            }

            Ok(Rc::new(Value::Record(record_map)))
        }
        TypedKind::Block(statements, tail) => {
            let mut block_env = env.clone();

            for TypedStatement { pattern, value, .. } in statements {
                let val = eval(value, &mut block_env, custom_fns)?;
                bind_pattern(pattern, val, &mut block_env)?;
            }

            match tail {
                Some(tail_expr) => eval(tail_expr, &mut block_env, custom_fns),
                None => Ok(Rc::new(Value::Unit)),
            }
        }
    }
}

/// Creates an initial empty environment and starts evaluation.
pub fn eval_expr(expr: &Typed) -> EvalResult {
    let mut initial_env = Environment::new();
    let custom_fns = CustomFnRegistry::new();
    eval(expr, &mut initial_env, &custom_fns)
}

pub fn eval_statement(
    env: &mut Environment,
    stmt: &TypedStatement,
    custom_fns: &CustomFnRegistry,
) -> EvalResult {
    let TypedStatement { value, pattern, .. } = stmt;
    let val = eval(value, env, custom_fns)?;
    bind_pattern(pattern, val.clone(), env)?;
    Ok(val)
}

pub fn eval_groups(
    env: &mut Environment,
    groups: Vec<TypedGroup>,
    custom_fns: &CustomFnRegistry,
) -> Result<(), EvalError> {
    for group in groups {
        match group {
            TypedGroup::NonRecursive(def) => {
                let val = eval(&def.expr, env, custom_fns)?;
                env.insert(def.name.0, val);
            }
            TypedGroup::Recursive(defs) => {
                let mut cells = HashMap::new();
                for def in &defs {
                    let cell = Rc::new(RefCell::new(Rc::new(Value::Unit)));
                    env.insert_cell(def.name.0, cell.clone());
                    cells.insert(def.name.0, cell);
                }

                for def in defs {
                    let val = eval(&def.expr, env, custom_fns)?;
                    let cell = cells.get(&def.name.0).unwrap();
                    *cell.borrow_mut() = val;
                }
            }
        }
    }
    Ok(())
}

pub fn run_main(
    env: &mut Environment,
    main_name: GlobalName,
    custom_fns: &CustomFnRegistry,
) -> EvalResult {
    let main_val = env
        .get(&main_name)
        .ok_or(EvalError::UndefinedVariable(main_name))?;

    apply(main_val, Rc::new(Value::Unit), env, custom_fns)
}

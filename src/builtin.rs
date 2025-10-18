use crate::analysis::inference::{Type, TypeScheme};
use phf::Map;
use phf_macros::phf_map;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BuiltinFn {
    IntAdd,
    IntSubtract,
    IntMultiply,
    IntDivide,

    FloatAdd,
    FloatSubtract,
    FloatMultiply,
    FloatDivide,

    IntEqual,
    IntNotEqual,
    IntLessEqual,
    IntGreaterEqual,
    IntLess,
    IntGreater,

    FloatEqual,
    FloatNotEqual,
    FloatLessEqual,
    FloatGreaterEqual,
    FloatLess,
    FloatGreater,

    BoolEqual,
    BoolNotEqual,

    IntNegate,
    FloatNegate,
    Not,

    StringConcat,

    Print,
    StringOfFloat,
    StringOfInt,
    FloatOfInt,
    Floor,
    Ceil,
}

pub static BUILTINS: Map<&'static str, BuiltinFn> = phf_map! {
    "print" => BuiltinFn::Print,
    "string_of_float" => BuiltinFn::StringOfFloat,
    "string_of_int" => BuiltinFn::StringOfInt,
    "float_of_int" => BuiltinFn::FloatOfInt,
    "floor" => BuiltinFn::Floor,
    "ceil" => BuiltinFn::Ceil,

    "+" => BuiltinFn::IntAdd,
    "-" => BuiltinFn::IntSubtract,
    "*" => BuiltinFn::IntMultiply,
    "/" => BuiltinFn::IntDivide,

    "+." => BuiltinFn::FloatAdd,
    "-." => BuiltinFn::FloatSubtract,
    "*." => BuiltinFn::FloatMultiply,
    "/." => BuiltinFn::FloatDivide,

    "==" => BuiltinFn::IntEqual,
    "!=" => BuiltinFn::IntNotEqual,
    ">=" => BuiltinFn::IntGreaterEqual,
    "<=" => BuiltinFn::IntLessEqual,
    ">" => BuiltinFn::IntGreater,
    "<" => BuiltinFn::IntLess,

    "==." => BuiltinFn::FloatEqual,
    "!=." => BuiltinFn::FloatNotEqual,
    ">=." => BuiltinFn::FloatGreaterEqual,
    "<=." => BuiltinFn::FloatLessEqual,
    ">." => BuiltinFn::FloatGreater,
    "<." => BuiltinFn::FloatLess,

    "==b" => BuiltinFn::BoolEqual,
    "!=b" => BuiltinFn::BoolNotEqual,

    "~" => BuiltinFn::IntNegate,
    "~." => BuiltinFn::FloatNegate,
    "!" => BuiltinFn::Not,

    "^" => BuiltinFn::StringConcat,
};

fn mono(ty: Type) -> TypeScheme {
    TypeScheme {
        vars: vec![],
        ty: Rc::new(ty),
    }
}

fn func(a: Type, b: Type) -> Type {
    Type::Function(Rc::new(a), Rc::new(b))
}

pub fn builtin_type(builtin: &BuiltinFn) -> TypeScheme {
    use BuiltinFn::*;

    match builtin {
        IntAdd | IntSubtract | IntMultiply | IntDivide => {
            mono(func(Type::Int, func(Type::Int, Type::Int)))
        }
        FloatAdd | FloatSubtract | FloatMultiply | FloatDivide => {
            mono(func(Type::Float, func(Type::Float, Type::Float)))
        }

        IntEqual | IntNotEqual | IntLessEqual | IntGreaterEqual | IntLess | IntGreater => {
            mono(func(Type::Int, func(Type::Int, Type::Bool)))
        }
        FloatEqual | FloatNotEqual | FloatLessEqual | FloatGreaterEqual | FloatLess
        | FloatGreater => mono(func(Type::Float, func(Type::Float, Type::Bool))),
        BoolEqual | BoolNotEqual => mono(func(Type::Bool, func(Type::Bool, Type::Bool))),

        IntNegate => mono(func(Type::Int, Type::Int)),
        FloatNegate => mono(func(Type::Float, Type::Float)),
        Not => mono(func(Type::Bool, Type::Bool)),

        StringConcat => mono(func(Type::String, func(Type::String, Type::String))),

        Print => mono(func(Type::String, Type::String)),
        StringOfFloat => mono(func(Type::Float, Type::String)),
        StringOfInt => mono(func(Type::Int, Type::String)),
        FloatOfInt => mono(func(Type::Int, Type::Float)),
        Floor => mono(func(Type::Float, Type::Int)),
        Ceil => mono(func(Type::Float, Type::Int)),
    }
}

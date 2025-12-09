use crate::analysis::inference::{Type, TypeScheme};
use crate::analysis::resolver::DefID;
use crate::builtin::BuiltinFn::{
    BoolEqual, BoolNotEqual, Ceil, FloatAdd, FloatDivide, FloatEqual, FloatGreater,
    FloatGreaterEqual, FloatLess, FloatLessEqual, FloatMultiply, FloatNegate, FloatNotEqual,
    FloatOfInt, FloatSubtract, Floor, IntAdd, IntDivide, IntEqual, IntGreater, IntGreaterEqual,
    IntLess, IntLessEqual, IntMultiply, IntNegate, IntNotEqual, IntSubtract, Not, Print,
    StringConcat, StringOfFloat, StringOfInt, TimeMicro,
};
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
    TimeMicro,
}

pub static BUILTINS: Map<&'static str, BuiltinFn> = phf_map! {
    "print" => BuiltinFn::Print,
    "string_of_float" => BuiltinFn::StringOfFloat,
    "string_of_int" => BuiltinFn::StringOfInt,
    "float_of_int" => BuiltinFn::FloatOfInt,
    "floor" => BuiltinFn::Floor,
    "ceil" => BuiltinFn::Ceil,
    "time_micro" => BuiltinFn::TimeMicro,

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

pub static INT_TYPE: DefID = DefID(0);
pub static FLOAT_TYPE: DefID = DefID(1);
pub static BOOL_TYPE: DefID = DefID(2);
pub static STRING_TYPE: DefID = DefID(3);
pub static UNIT_TYPE: DefID = DefID(4);
pub static LIST_TYPE: DefID = DefID(5);

pub static BUILTINS_TYPES: Map<&'static str, DefID> = phf_map! {
    "int" => INT_TYPE,
    "float" => FLOAT_TYPE,
    "bool" => BOOL_TYPE,
    "string" => STRING_TYPE,
    "unit" => UNIT_TYPE,
    "list" => LIST_TYPE,
};

pub static TYPE_BASE: DefID = DefID(BUILTINS_TYPES.len());

impl BuiltinFn {
    pub fn type_scheme(&self) -> TypeScheme {
        use BuiltinFn::*;

        match self {
            IntAdd | IntSubtract | IntMultiply | IntDivide => mono(func(
                Type::Con(INT_TYPE),
                func(Type::Con(INT_TYPE), Type::Con(INT_TYPE)),
            )),
            FloatAdd | FloatSubtract | FloatMultiply | FloatDivide => mono(func(
                Type::Con(FLOAT_TYPE),
                func(Type::Con(FLOAT_TYPE), Type::Con(FLOAT_TYPE)),
            )),

            IntEqual | IntNotEqual | IntLessEqual | IntGreaterEqual | IntLess | IntGreater => {
                mono(func(
                    Type::Con(INT_TYPE),
                    func(Type::Con(INT_TYPE), Type::Con(BOOL_TYPE)),
                ))
            }
            FloatEqual | FloatNotEqual | FloatLessEqual | FloatGreaterEqual | FloatLess
            | FloatGreater => mono(func(
                Type::Con(FLOAT_TYPE),
                func(Type::Con(FLOAT_TYPE), Type::Con(BOOL_TYPE)),
            )),
            BoolEqual | BoolNotEqual => mono(func(
                Type::Con(BOOL_TYPE),
                func(Type::Con(BOOL_TYPE), Type::Con(BOOL_TYPE)),
            )),

            IntNegate => mono(func(Type::Con(INT_TYPE), Type::Con(INT_TYPE))),
            FloatNegate => mono(func(Type::Con(FLOAT_TYPE), Type::Con(FLOAT_TYPE))),
            Not => mono(func(Type::Con(BOOL_TYPE), Type::Con(BOOL_TYPE))),

            StringConcat => mono(func(
                Type::Con(STRING_TYPE),
                func(Type::Con(STRING_TYPE), Type::Con(STRING_TYPE)),
            )),

            Print => mono(func(Type::Con(STRING_TYPE), Type::Con(STRING_TYPE))),
            StringOfFloat => mono(func(Type::Con(FLOAT_TYPE), Type::Con(STRING_TYPE))),
            StringOfInt => mono(func(Type::Con(INT_TYPE), Type::Con(STRING_TYPE))),
            FloatOfInt => mono(func(Type::Con(INT_TYPE), Type::Con(FLOAT_TYPE))),
            Floor => mono(func(Type::Con(FLOAT_TYPE), Type::Con(INT_TYPE))),
            Ceil => mono(func(Type::Con(FLOAT_TYPE), Type::Con(INT_TYPE))),
            TimeMicro => mono(func(Type::Con(UNIT_TYPE), Type::Con(INT_TYPE))),
        }
    }
}

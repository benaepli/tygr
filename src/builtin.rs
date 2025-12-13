use crate::analysis::inference::{Type, TypeScheme};
use crate::analysis::resolver::TypeName;
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

pub static INT_TYPE: TypeName = TypeName(0);
pub static FLOAT_TYPE: TypeName = TypeName(1);
pub static BOOL_TYPE: TypeName = TypeName(2);
pub static STRING_TYPE: TypeName = TypeName(3);
pub static UNIT_TYPE: TypeName = TypeName(4);
pub static LIST_TYPE: TypeName = TypeName(5);

pub static BUILTIN_TYPES: Map<&'static str, TypeName> = phf_map! {
    "int" => INT_TYPE,
    "float" => FLOAT_TYPE,
    "bool" => BOOL_TYPE,
    "string" => STRING_TYPE,
    "unit" => UNIT_TYPE,
    "list" => LIST_TYPE,
};

pub static TYPE_BASE: TypeName = TypeName(BUILTIN_TYPES.len());

impl BuiltinFn {
    pub fn type_scheme(&self) -> TypeScheme {
        use BuiltinFn::*;

        match self {
            IntAdd | IntSubtract | IntMultiply | IntDivide => mono(func(
                Type::Star(INT_TYPE),
                func(Type::Star(INT_TYPE), Type::Star(INT_TYPE)),
            )),
            FloatAdd | FloatSubtract | FloatMultiply | FloatDivide => mono(func(
                Type::Star(FLOAT_TYPE),
                func(Type::Star(FLOAT_TYPE), Type::Star(FLOAT_TYPE)),
            )),

            IntEqual | IntNotEqual | IntLessEqual | IntGreaterEqual | IntLess | IntGreater => {
                mono(func(
                    Type::Star(INT_TYPE),
                    func(Type::Star(INT_TYPE), Type::Star(BOOL_TYPE)),
                ))
            }
            FloatEqual | FloatNotEqual | FloatLessEqual | FloatGreaterEqual | FloatLess
            | FloatGreater => mono(func(
                Type::Star(FLOAT_TYPE),
                func(Type::Star(FLOAT_TYPE), Type::Star(BOOL_TYPE)),
            )),
            BoolEqual | BoolNotEqual => mono(func(
                Type::Star(BOOL_TYPE),
                func(Type::Star(BOOL_TYPE), Type::Star(BOOL_TYPE)),
            )),

            IntNegate => mono(func(Type::Star(INT_TYPE), Type::Star(INT_TYPE))),
            FloatNegate => mono(func(Type::Star(FLOAT_TYPE), Type::Star(FLOAT_TYPE))),
            Not => mono(func(Type::Star(BOOL_TYPE), Type::Star(BOOL_TYPE))),

            StringConcat => mono(func(
                Type::Star(STRING_TYPE),
                func(Type::Star(STRING_TYPE), Type::Star(STRING_TYPE)),
            )),

            Print => mono(func(Type::Star(STRING_TYPE), Type::Star(STRING_TYPE))),
            StringOfFloat => mono(func(Type::Star(FLOAT_TYPE), Type::Star(STRING_TYPE))),
            StringOfInt => mono(func(Type::Star(INT_TYPE), Type::Star(STRING_TYPE))),
            FloatOfInt => mono(func(Type::Star(INT_TYPE), Type::Star(FLOAT_TYPE))),
            Floor => mono(func(Type::Star(FLOAT_TYPE), Type::Star(INT_TYPE))),
            Ceil => mono(func(Type::Star(FLOAT_TYPE), Type::Star(INT_TYPE))),
            TimeMicro => mono(func(Type::Star(UNIT_TYPE), Type::Star(INT_TYPE))),
        }
    }
}

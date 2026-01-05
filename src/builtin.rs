use crate::analysis::inference::{Kind, Type, TypeKind, TypeScheme};
use crate::analysis::resolver::{GlobalType, TypeName};
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

fn mono(ty: Rc<Type>) -> TypeScheme {
    TypeScheme { vars: vec![], ty }
}

fn con(name: TypeName) -> Rc<Type> {
    Type::simple(name)
}

fn func(a: Rc<Type>, b: Rc<Type>) -> Rc<Type> {
    Type::new(
        TypeKind::Function(a.clone(), b.clone()),
        Rc::new(Kind::Star),
    )
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

pub fn builtin_kinds(gt: GlobalType) -> Option<Rc<Kind>> {
    if gt.krate.is_some() {
        return None;
    }

    let name = gt.name;
    if name == INT_TYPE
        || name == FLOAT_TYPE
        || name == BOOL_TYPE
        || name == STRING_TYPE
        || name == UNIT_TYPE
    {
        Some(Rc::new(Kind::Star))
    } else if name == LIST_TYPE {
        Some(Rc::new(Kind::Arrow(
            Rc::new(Kind::Star),
            Rc::new(Kind::Star),
        )))
    } else {
        None
    }
}

pub static TYPE_BASE: TypeName = TypeName(BUILTIN_TYPES.len());

impl BuiltinFn {
    pub fn type_scheme(&self) -> TypeScheme {
        use BuiltinFn::*;

        match self {
            IntAdd | IntSubtract | IntMultiply | IntDivide => {
                mono(func(con(INT_TYPE), func(con(INT_TYPE), con(INT_TYPE))))
            }
            FloatAdd | FloatSubtract | FloatMultiply | FloatDivide => mono(func(
                con(FLOAT_TYPE),
                func(con(FLOAT_TYPE), con(FLOAT_TYPE)),
            )),

            IntEqual | IntNotEqual | IntLessEqual | IntGreaterEqual | IntLess | IntGreater => {
                mono(func(con(INT_TYPE), func(con(INT_TYPE), con(BOOL_TYPE))))
            }
            FloatEqual | FloatNotEqual | FloatLessEqual | FloatGreaterEqual | FloatLess
            | FloatGreater => mono(func(con(FLOAT_TYPE), func(con(FLOAT_TYPE), con(BOOL_TYPE)))),
            BoolEqual | BoolNotEqual => {
                mono(func(con(BOOL_TYPE), func(con(BOOL_TYPE), con(BOOL_TYPE))))
            }

            IntNegate => mono(func(con(INT_TYPE), con(INT_TYPE))),
            FloatNegate => mono(func(con(FLOAT_TYPE), con(FLOAT_TYPE))),
            Not => mono(func(con(BOOL_TYPE), con(BOOL_TYPE))),

            StringConcat => mono(func(
                con(STRING_TYPE),
                func(con(STRING_TYPE), con(STRING_TYPE)),
            )),

            Print => mono(func(con(STRING_TYPE), con(STRING_TYPE))),
            StringOfFloat => mono(func(con(FLOAT_TYPE), con(STRING_TYPE))),
            StringOfInt => mono(func(con(INT_TYPE), con(STRING_TYPE))),
            FloatOfInt => mono(func(con(INT_TYPE), con(FLOAT_TYPE))),
            Floor => mono(func(con(FLOAT_TYPE), con(INT_TYPE))),
            Ceil => mono(func(con(FLOAT_TYPE), con(INT_TYPE))),
            TimeMicro => mono(func(con(UNIT_TYPE), con(INT_TYPE))),
        }
    }
}

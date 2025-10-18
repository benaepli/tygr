use phf::Map;
use phf_macros::phf_map;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum BuiltinFn {
    IntEq,
    FloatEq,
    BoolEq,
    IntGeq,
    IntLeq,
    IntGreater,
    IntLess,
    FloatGeq,
    FloatLeq,
    FloatGreater,
    FloatLess,

    Print,
    StringOfFloat,
    StringOfInt,
}

pub static BUILTINS: Map<&'static str, BuiltinFn> = phf_map! {
    "print" => BuiltinFn::Print,
    "string_of_float" => BuiltinFn::StringOfFloat,
    "string_of_int" => BuiltinFn::StringOfInt,

    "int_eq" => BuiltinFn::IntEq,
    "int_geq" => BuiltinFn::IntGeq,
    "int_leq" => BuiltinFn::IntLeq,
    "int_greater" => BuiltinFn::IntGreater,
    "int_less" => BuiltinFn::IntLess,

    "float_eq" => BuiltinFn::FloatEq,
    "float_geq" => BuiltinFn::FloatGeq,
    "float_leq" => BuiltinFn::FloatLeq,
    "float_greater" => BuiltinFn::FloatGreater,
    "float_less" => BuiltinFn::FloatLess,

    "bool_eq" => BuiltinFn::BoolEq,
};

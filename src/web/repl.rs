use crate::analysis::inference::{Kind, Type, TypeKind, TypeScheme};
use crate::analysis::resolver::GlobalType;
use crate::builtin::{BOOL_TYPE, FLOAT_TYPE, INT_TYPE, LIST_TYPE, STRING_TYPE, UNIT_TYPE};
use crate::custom::CustomFn;
use crate::interpreter::{Environment, EvalError, EvalResult, Value};
use crate::repl;
use codespan_reporting::term::termcolor::{Color, ColorSpec, WriteColor};
use js_sys::{Array, Function};
use serde::Serialize;
use std::io;
use std::rc::Rc;
use wasm_bindgen::prelude::*;

#[wasm_bindgen]
pub struct WasmRepl {
    repl: repl::Repl,
}

#[wasm_bindgen]
impl WasmRepl {
    #[wasm_bindgen(constructor)]
    pub fn new() -> Self {
        Self {
            repl: repl::Repl::default(),
        }
    }

    pub fn eval(&mut self, source: &str) -> JsValue {
        let mut writer = CapturingWriter::new();
        self.repl.process_line(source, &mut writer);
        serde_wasm_bindgen::to_value(&writer.spans).unwrap()
    }

    /// Register a custom function from JavaScript using a simple type signature.
    #[wasm_bindgen(js_name = registerCustomFn)]
    pub fn register_custom_fn(
        &mut self,
        name: String,
        arity: usize,
        type_sig: Vec<String>,
        callback: Function,
    ) -> Result<(), JsError> {
        let scheme = parse_type_signature(&type_sig)?;

        let js_custom_fn = JsCustomFn {
            name,
            arity,
            scheme,
            callback,
        };

        self.repl
            .register_custom_fn(js_custom_fn)
            .map_err(|e| JsError::new(&e.to_string()))
    }

    /// Register a custom function with a full TypeScheme (for advanced use).
    ///
    /// The type_scheme should be a JSON object matching the TypeScheme structure.
    #[wasm_bindgen(js_name = registerCustomFnWithScheme)]
    pub fn register_custom_fn_with_scheme(
        &mut self,
        name: String,
        arity: usize,
        type_scheme: JsValue,
        callback: Function,
    ) -> Result<(), JsError> {
        let scheme: TypeScheme = serde_wasm_bindgen::from_value(type_scheme)
            .map_err(|e| JsError::new(&format!("Invalid type scheme: {}", e)))?;

        let js_custom_fn = JsCustomFn {
            name,
            arity,
            scheme,
            callback,
        };

        self.repl
            .register_custom_fn(js_custom_fn)
            .map_err(|e| JsError::new(&e.to_string()))
    }
}

fn parse_type_signature(type_sig: &[String]) -> Result<TypeScheme, JsError> {
    if type_sig.is_empty() {
        return Err(JsError::new("Type signature cannot be empty"));
    }

    let types: Result<Vec<Rc<Type>>, JsError> =
        type_sig.iter().map(|s| parse_simple_type(s)).collect();
    let types = types?;

    // Build function type from right to left: [A, B, C] -> A -> B -> C
    let mut result_ty = types.last().unwrap().clone();
    for ty in types.iter().rev().skip(1) {
        result_ty = Type::new(
            TypeKind::Function(ty.clone(), result_ty),
            Rc::new(Kind::Star),
        );
    }

    Ok(TypeScheme {
        vars: vec![],
        ty: result_ty,
    })
}

fn parse_simple_type(s: &str) -> Result<Rc<Type>, JsError> {
    match s {
        "int" => Ok(Type::simple(INT_TYPE)),
        "float" => Ok(Type::simple(FLOAT_TYPE)),
        "bool" => Ok(Type::simple(BOOL_TYPE)),
        "string" => Ok(Type::simple(STRING_TYPE)),
        "unit" => Ok(Type::simple(UNIT_TYPE)),
        s if s.starts_with('[') && s.ends_with(']') => {
            let inner = &s[1..s.len() - 1];
            let inner_ty = parse_simple_type(inner)?;
            let list_con = Type::new(
                TypeKind::Con(GlobalType {
                    krate: None,
                    name: LIST_TYPE,
                }),
                Rc::new(Kind::Arrow(Rc::new(Kind::Star), Rc::new(Kind::Star))),
            );
            Ok(Type::new(
                TypeKind::App(list_con, inner_ty),
                Rc::new(Kind::Star),
            ))
        }
        _ => Err(JsError::new(&format!("Unknown type: {}", s))),
    }
}

/// A custom function backed by a JavaScript callback.
struct JsCustomFn {
    name: String,
    arity: usize,
    scheme: TypeScheme,
    callback: Function,
}

impl CustomFn for JsCustomFn {
    fn name(&self) -> &str {
        &self.name
    }

    fn arity(&self) -> usize {
        self.arity
    }

    fn type_scheme(&self) -> TypeScheme {
        self.scheme.clone()
    }

    fn call(&self, args: &[Rc<Value>], _env: &mut Environment) -> EvalResult {
        let js_args = Array::new();
        for arg in args {
            let js_val = value_to_js(arg);
            js_args.push(&js_val);
        }

        let result = self.callback.apply(&JsValue::NULL, &js_args).map_err(|e| {
            EvalError::TypeMismatch(format!(
                "JS callback error: {:?}",
                e.as_string().unwrap_or_default()
            ))
        })?;

        js_to_value(result)
    }
}

fn value_to_js(value: &Value) -> JsValue {
    serde_wasm_bindgen::to_value(value).unwrap_or(JsValue::NULL)
}

fn js_to_value(js: JsValue) -> EvalResult {
    serde_wasm_bindgen::from_value::<Value>(js)
        .map(|v| Rc::new(v))
        .map_err(|e| EvalError::TypeMismatch(format!("Cannot convert JS value: {}", e)))
}

#[derive(Serialize, Clone)]
pub struct StyledSpan {
    pub text: String,
    pub fg: Option<String>,
    pub bg: Option<String>,
    pub bold: bool,
    pub italic: bool,
    pub intense: bool,
    pub dimmed: bool,
}

pub struct CapturingWriter {
    pub spans: Vec<StyledSpan>,
    current_style: ColorSpec,
}

impl CapturingWriter {
    pub fn new() -> Self {
        Self {
            spans: Vec::new(),
            current_style: ColorSpec::new(),
        }
    }

    fn color_to_string(c: &Color) -> String {
        match c {
            Color::Black => "black",
            Color::Blue => "blue",
            Color::Green => "green",
            Color::Red => "red",
            Color::Cyan => "cyan",
            Color::Magenta => "magenta",
            Color::Yellow => "yellow",
            Color::White => "white",
            _ => "default",
        }
        .to_string()
    }
}

impl io::Write for CapturingWriter {
    fn write(&mut self, buf: &[u8]) -> io::Result<usize> {
        let text_chunk = String::from_utf8_lossy(buf).to_string();

        if text_chunk.is_empty() {
            return Ok(buf.len());
        }

        let should_append = if let Some(last) = self.spans.last() {
            let fg_match = last.fg == self.current_style.fg().map(Self::color_to_string);
            let bg_match = last.bg == self.current_style.bg().map(Self::color_to_string);
            let bold_match = last.bold == self.current_style.bold();
            let italic_match = last.italic == self.current_style.italic();

            fg_match && bg_match && bold_match && italic_match
        } else {
            false
        };

        if should_append {
            if let Some(last) = self.spans.last_mut() {
                last.text.push_str(&text_chunk);
            }
        } else {
            let span = StyledSpan {
                text: text_chunk,
                fg: self.current_style.fg().map(Self::color_to_string),
                bg: self.current_style.bg().map(Self::color_to_string),
                bold: self.current_style.bold(),
                italic: self.current_style.italic(),
                intense: self.current_style.intense(),
                dimmed: self.current_style.dimmed(),
            };
            self.spans.push(span);
        }

        Ok(buf.len())
    }

    fn flush(&mut self) -> io::Result<()> {
        Ok(())
    }
}

impl WriteColor for CapturingWriter {
    fn supports_color(&self) -> bool {
        true
    }

    fn set_color(&mut self, spec: &ColorSpec) -> io::Result<()> {
        self.current_style = spec.clone();
        Ok(())
    }

    fn reset(&mut self) -> io::Result<()> {
        self.current_style = ColorSpec::new();
        Ok(())
    }
}

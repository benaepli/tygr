use crate::repl;
use codespan_reporting::term::termcolor::{Color, ColorSpec, WriteColor};
use serde::Serialize;
use std::io;
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

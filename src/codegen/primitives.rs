use cranelift::prelude::*;
use cranelift_module::Module;

use super::FnCompiler;

impl<'a, M: Module> FnCompiler<'a, M> {
    /// Emit inline Cranelift IR for a builtin primitive by name or mangled name.
    /// Returns None if the name isn't a known inline primitive.
    pub(crate) fn compile_inline_primitive(&mut self, name: &str, args: &[Value]) -> Option<Value> {
        if args.len() != 2 {
            return None;
        }
        let (l, r) = (args[0], args[1]);
        match name {
            // Mangled trait dispatch names (e.g., +$Int from prelude impl)
            "+$Int" | "add-i64" => Some(self.builder.ins().iadd(l, r)),
            "-$Int" | "sub-i64" => Some(self.builder.ins().isub(l, r)),
            "*$Int" | "mul-i64" => Some(self.builder.ins().imul(l, r)),
            "/$Int" | "div-i64" => Some(self.builder.ins().sdiv(l, r)),
            "=$Int" | "eq-i64" => {
                let cmp = self.builder.ins().icmp(IntCC::Equal, l, r);
                Some(self.builder.ins().uextend(types::I64, cmp))
            }
            "<$Int" | "lt-i64" => {
                let cmp = self.builder.ins().icmp(IntCC::SignedLessThan, l, r);
                Some(self.builder.ins().uextend(types::I64, cmp))
            }
            ">$Int" | "gt-i64" => {
                let cmp = self.builder.ins().icmp(IntCC::SignedGreaterThan, l, r);
                Some(self.builder.ins().uextend(types::I64, cmp))
            }
            "<=$Int" | "le-i64" => {
                let cmp = self.builder.ins().icmp(IntCC::SignedLessThanOrEqual, l, r);
                Some(self.builder.ins().uextend(types::I64, cmp))
            }
            ">=$Int" | "ge-i64" => {
                let cmp = self
                    .builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, l, r);
                Some(self.builder.ins().uextend(types::I64, cmp))
            }
            // Float inline primitives: bitcast i64→f64, operate, bitcast f64→i64
            "+$Float" | "add-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fadd(lf, rf);
                Some(self.builder.ins().bitcast(types::I64, MemFlags::new(), res))
            }
            "-$Float" | "sub-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fsub(lf, rf);
                Some(self.builder.ins().bitcast(types::I64, MemFlags::new(), res))
            }
            "*$Float" | "mul-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fmul(lf, rf);
                Some(self.builder.ins().bitcast(types::I64, MemFlags::new(), res))
            }
            "/$Float" | "div-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fdiv(lf, rf);
                Some(self.builder.ins().bitcast(types::I64, MemFlags::new(), res))
            }
            "=$Float" | "eq-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let cmp = self.builder.ins().fcmp(FloatCC::Equal, lf, rf);
                Some(self.builder.ins().uextend(types::I64, cmp))
            }
            "<$Float" | "lt-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let cmp = self.builder.ins().fcmp(FloatCC::LessThan, lf, rf);
                Some(self.builder.ins().uextend(types::I64, cmp))
            }
            ">$Float" | "gt-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let cmp = self.builder.ins().fcmp(FloatCC::GreaterThan, lf, rf);
                Some(self.builder.ins().uextend(types::I64, cmp))
            }
            "<=$Float" | "le-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let cmp = self.builder.ins().fcmp(FloatCC::LessThanOrEqual, lf, rf);
                Some(self.builder.ins().uextend(types::I64, cmp))
            }
            ">=$Float" | "ge-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let cmp = self.builder.ins().fcmp(FloatCC::GreaterThanOrEqual, lf, rf);
                Some(self.builder.ins().uextend(types::I64, cmp))
            }
            _ => None,
        }
    }
}

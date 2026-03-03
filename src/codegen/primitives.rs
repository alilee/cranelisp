use cranelift::prelude::*;
use cranelift_module::Module;

use crate::error::{CranelispError, Span};

use super::FnCompiler;

impl<'a, M: Module> FnCompiler<'a, M> {
    /// Emit inline Cranelift IR for a builtin primitive by name or mangled name.
    /// Returns Ok(None) if the name isn't a known inline primitive.
    /// Num trait integer ops emit checked arithmetic (panic on overflow/div-by-zero).
    /// Raw primitives (add-i64 etc.) remain unchecked.
    pub(crate) fn compile_inline_primitive(
        &mut self,
        name: &str,
        args: &[Value],
        span: Span,
    ) -> Result<Option<Value>, CranelispError> {
        if args.len() != 2 {
            return Ok(None);
        }
        let (l, r) = (args[0], args[1]);
        match name {
            // Checked integer arithmetic (Num trait)
            "Num.+$Int" => Ok(Some(self.emit_checked_add(l, r, span)?)),
            "Num.-$Int" => Ok(Some(self.emit_checked_sub(l, r, span)?)),
            "Num.*$Int" => Ok(Some(self.emit_checked_mul(l, r, span)?)),
            "Num./$Int" => Ok(Some(self.emit_checked_div(l, r, span)?)),

            // Unchecked trait + raw primitives (wrapping/trapping)
            "Unchecked.+$Int" | "add-i64" => Ok(Some(self.builder.ins().iadd(l, r))),
            "Unchecked.-$Int" | "sub-i64" => Ok(Some(self.builder.ins().isub(l, r))),
            "Unchecked.*$Int" | "mul-i64" => Ok(Some(self.builder.ins().imul(l, r))),
            "Unchecked./$Int" | "div-i64" => Ok(Some(self.builder.ins().sdiv(l, r))),

            // Integer comparison (no overflow concerns)
            "Eq.=$Int" | "eq-i64" => {
                let cmp = self.builder.ins().icmp(IntCC::Equal, l, r);
                Ok(Some(self.builder.ins().uextend(types::I64, cmp)))
            }
            "Ord.<$Int" | "lt-i64" => {
                let cmp = self.builder.ins().icmp(IntCC::SignedLessThan, l, r);
                Ok(Some(self.builder.ins().uextend(types::I64, cmp)))
            }
            "Ord.>$Int" | "gt-i64" => {
                let cmp = self.builder.ins().icmp(IntCC::SignedGreaterThan, l, r);
                Ok(Some(self.builder.ins().uextend(types::I64, cmp)))
            }
            "Ord.<=$Int" | "le-i64" => {
                let cmp = self
                    .builder
                    .ins()
                    .icmp(IntCC::SignedLessThanOrEqual, l, r);
                Ok(Some(self.builder.ins().uextend(types::I64, cmp)))
            }
            "Ord.>=$Int" | "ge-i64" => {
                let cmp = self
                    .builder
                    .ins()
                    .icmp(IntCC::SignedGreaterThanOrEqual, l, r);
                Ok(Some(self.builder.ins().uextend(types::I64, cmp)))
            }
            // Float inline primitives: bitcast i64→f64, operate, bitcast f64→i64
            // IEEE 754 handles edge cases (infinity, NaN) — no checked variants needed.
            "Num.+$Float" | "add-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fadd(lf, rf);
                Ok(Some(
                    self.builder.ins().bitcast(types::I64, MemFlags::new(), res),
                ))
            }
            "Num.-$Float" | "sub-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fsub(lf, rf);
                Ok(Some(
                    self.builder.ins().bitcast(types::I64, MemFlags::new(), res),
                ))
            }
            "Num.*$Float" | "mul-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fmul(lf, rf);
                Ok(Some(
                    self.builder.ins().bitcast(types::I64, MemFlags::new(), res),
                ))
            }
            "Num./$Float" | "div-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fdiv(lf, rf);
                Ok(Some(
                    self.builder.ins().bitcast(types::I64, MemFlags::new(), res),
                ))
            }
            "Eq.=$Float" | "eq-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let cmp = self.builder.ins().fcmp(FloatCC::Equal, lf, rf);
                Ok(Some(self.builder.ins().uextend(types::I64, cmp)))
            }
            "Ord.<$Float" | "lt-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let cmp = self.builder.ins().fcmp(FloatCC::LessThan, lf, rf);
                Ok(Some(self.builder.ins().uextend(types::I64, cmp)))
            }
            "Ord.>$Float" | "gt-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let cmp = self.builder.ins().fcmp(FloatCC::GreaterThan, lf, rf);
                Ok(Some(self.builder.ins().uextend(types::I64, cmp)))
            }
            "Ord.<=$Float" | "le-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let cmp = self.builder.ins().fcmp(FloatCC::LessThanOrEqual, lf, rf);
                Ok(Some(self.builder.ins().uextend(types::I64, cmp)))
            }
            "Ord.>=$Float" | "ge-f64" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let cmp = self
                    .builder
                    .ins()
                    .fcmp(FloatCC::GreaterThanOrEqual, lf, rf);
                Ok(Some(self.builder.ins().uextend(types::I64, cmp)))
            }
            // Unchecked float: same as Num float (IEEE 754)
            "Unchecked.+$Float" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fadd(lf, rf);
                Ok(Some(
                    self.builder.ins().bitcast(types::I64, MemFlags::new(), res),
                ))
            }
            "Unchecked.-$Float" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fsub(lf, rf);
                Ok(Some(
                    self.builder.ins().bitcast(types::I64, MemFlags::new(), res),
                ))
            }
            "Unchecked.*$Float" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fmul(lf, rf);
                Ok(Some(
                    self.builder.ins().bitcast(types::I64, MemFlags::new(), res),
                ))
            }
            "Unchecked./$Float" => {
                let lf = self.builder.ins().bitcast(types::F64, MemFlags::new(), l);
                let rf = self.builder.ins().bitcast(types::F64, MemFlags::new(), r);
                let res = self.builder.ins().fdiv(lf, rf);
                Ok(Some(
                    self.builder.ins().bitcast(types::I64, MemFlags::new(), res),
                ))
            }
            // IO bind: allocate Bind node [tag=2, inner_io, cont_closure]
            "bind" => {
                let ptr = self.compile_alloc(24, span)?; // 3 x i64
                let tag_val = self.builder.ins().iconst(types::I64, 2); // Bind tag
                self.builder
                    .ins()
                    .store(MemFlags::trusted(), tag_val, ptr, 0);
                self.builder
                    .ins()
                    .store(MemFlags::trusted(), l, ptr, 8); // inner IO value
                self.builder
                    .ins()
                    .store(MemFlags::trusted(), r, ptr, 16); // cont closure
                // Inc both args: the Bind node holds references to them
                self.emit_inc_inline(l);
                self.emit_inc_inline(r);
                Ok(Some(ptr))
            }

            _ => Ok(None),
        }
    }

    /// Emit a panic block and branch to it on condition, otherwise continue.
    /// Returns the continue_block. Builder is left positioned at continue_block.
    fn emit_checked_branch(
        &mut self,
        overflow_flag: Value,
        msg: &str,
        span: Span,
    ) -> Result<Block, CranelispError> {
        let panic_block = self.builder.create_block();
        let continue_block = self.builder.create_block();

        self.builder
            .ins()
            .brif(overflow_flag, panic_block, &[], continue_block, &[]);

        // Panic block
        self.builder.switch_to_block(panic_block);
        self.builder.seal_block(panic_block);
        self.emit_panic_with_message(msg, span)?;
        self.builder.ins().trap(TrapCode::user(1).unwrap());

        // Continue block
        self.builder.switch_to_block(continue_block);
        self.builder.seal_block(continue_block);
        Ok(continue_block)
    }

    /// Checked integer addition: panics on overflow.
    fn emit_checked_add(
        &mut self,
        l: Value,
        r: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let result = self.builder.ins().iadd(l, r);
        // Overflow when both operands have the same sign but result differs:
        // overflow = (l ^ result) & (r ^ result), check sign bit
        let xor1 = self.builder.ins().bxor(l, result);
        let xor2 = self.builder.ins().bxor(r, result);
        let overflow = self.builder.ins().band(xor1, xor2);
        let sign = self.builder.ins().ushr_imm(overflow, 63);
        self.emit_checked_branch(sign, "integer overflow in +", span)?;
        Ok(result)
    }

    /// Checked integer subtraction: panics on overflow.
    fn emit_checked_sub(
        &mut self,
        l: Value,
        r: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let result = self.builder.ins().isub(l, r);
        // Overflow when operands have different signs and result sign differs from l:
        // overflow = (l ^ result) & (l ^ r), check sign bit
        let xor1 = self.builder.ins().bxor(l, result);
        let xor2 = self.builder.ins().bxor(l, r);
        let overflow = self.builder.ins().band(xor1, xor2);
        let sign = self.builder.ins().ushr_imm(overflow, 63);
        self.emit_checked_branch(sign, "integer overflow in -", span)?;
        Ok(result)
    }

    /// Checked integer multiplication: panics on overflow.
    fn emit_checked_mul(
        &mut self,
        l: Value,
        r: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let result = self.builder.ins().imul(l, r);
        // Check high bits: smulhi gives the upper 64 bits of the 128-bit result.
        // If result sign-extended matches, no overflow.
        let hi = self.builder.ins().smulhi(l, r);
        let expected_hi = self.builder.ins().sshr_imm(result, 63);
        let overflow = self
            .builder
            .ins()
            .icmp(IntCC::NotEqual, hi, expected_hi);
        self.emit_checked_branch(overflow, "integer overflow in *", span)?;
        Ok(result)
    }

    /// Checked integer division: panics on div-by-zero and MIN/-1 overflow.
    fn emit_checked_div(
        &mut self,
        l: Value,
        r: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Check 1: division by zero
        let zero = self.builder.ins().iconst(types::I64, 0);
        let is_zero = self.builder.ins().icmp(IntCC::Equal, r, zero);
        let check_overflow_block = self.builder.create_block();
        let panic_divzero = self.builder.create_block();

        self.builder.ins().brif(
            is_zero,
            panic_divzero,
            &[],
            check_overflow_block,
            &[],
        );

        // Panic block: division by zero
        self.builder.switch_to_block(panic_divzero);
        self.builder.seal_block(panic_divzero);
        self.emit_panic_with_message("integer division by zero", span)?;
        self.builder.ins().trap(TrapCode::user(1).unwrap());

        // Check 2: MIN / -1 overflow
        self.builder.switch_to_block(check_overflow_block);
        self.builder.seal_block(check_overflow_block);
        let min_val = self.builder.ins().iconst(types::I64, i64::MIN);
        let neg1 = self.builder.ins().iconst(types::I64, -1i64);
        let is_min = self.builder.ins().icmp(IntCC::Equal, l, min_val);
        let is_neg1 = self.builder.ins().icmp(IntCC::Equal, r, neg1);
        let both = self.builder.ins().band(is_min, is_neg1);
        self.emit_checked_branch(both, "integer overflow in /", span)?;

        let result = self.builder.ins().sdiv(l, r);
        Ok(result)
    }
}

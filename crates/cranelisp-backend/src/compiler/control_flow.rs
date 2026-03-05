// Control flow and binding codegen.
//
// compile_if, compile_let, compile_lambda

use cranelift::prelude::*;

use cranelisp_types::{CranelispError, Expr, Span, Symbol};

use super::FnCompiler;

impl<'a> FnCompiler<'a> {
    // --- Let expression ---

    pub(crate) fn compile_let(
        &mut self,
        bindings: &[(Symbol, Expr)],
        body: &Expr,
        _span: Span,
    ) -> Result<Value, CranelispError> {
        // Push a new scope frame.
        self.push_scope();

        // Compile each binding.
        let saved_tail = self.in_tail_position;
        self.in_tail_position = false;

        for (name, val_expr) in bindings {
            let val = self.compile_expr(val_expr)?;
            let var = self.fresh_variable();
            self.builder.declare_var(var, types::I64);
            self.builder.def_var(var, val);
            self.variables.insert(name.clone(), var);
            self.scope_stack
                .last_mut()
                .unwrap_or_else(|| unreachable!("invariant: scope_stack non-empty"))
                .push(name.clone());
        }

        // Body inherits tail position.
        self.in_tail_position = saved_tail;
        let result = self.compile_expr(body)?;

        // Pop the scope frame.
        self.pop_scope();

        Ok(result)
    }

    // --- If expression ---

    pub(crate) fn compile_if(
        &mut self,
        cond: &Expr,
        then_branch: &Expr,
        else_branch: &Expr,
    ) -> Result<Value, CranelispError> {
        let saved_tail = self.in_tail_position;

        // Condition is never in tail position.
        self.in_tail_position = false;
        let cond_val = self.compile_expr(cond)?;

        let then_block = self.builder.create_block();
        let else_block = self.builder.create_block();
        let merge_block = self.builder.create_block();
        self.builder.append_block_param(merge_block, types::I64);

        self.builder
            .ins()
            .brif(cond_val, then_block, &[], else_block, &[]);

        // Then branch.
        self.builder.switch_to_block(then_block);
        self.builder.seal_block(then_block);
        self.in_tail_position = saved_tail;
        let then_val = self.compile_expr(then_branch)?;
        self.builder.ins().jump(merge_block, &[then_val]);

        // Else branch.
        self.builder.switch_to_block(else_block);
        self.builder.seal_block(else_block);
        self.in_tail_position = saved_tail;
        let else_val = self.compile_expr(else_branch)?;
        self.builder.ins().jump(merge_block, &[else_val]);

        // Merge block.
        self.builder.switch_to_block(merge_block);
        self.builder.seal_block(merge_block);

        Ok(self.builder.block_params(merge_block)[0])
    }

    // --- Lambda expression ---

    pub(crate) fn compile_lambda(
        &mut self,
        _params: &[Symbol],
        _body: &Expr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        // Ring 0: Lambdas as first-class values require closures (Ring 1).
        // In Ring 0, lambdas only appear as the body of defn, which is
        // handled by compile_body. A bare lambda expression is an error.
        Err(CranelispError::CodegenError {
            message: "lambda expressions as values not supported in Ring 0 (closures require Ring 1)"
                .into(),
            span,
        })
    }
}

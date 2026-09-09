//! Private IO-node metadata emission shared by the backend producers.

use cranelift::prelude::*;
use cranelift_module::Module;
use cranelisp_types::{ConcreteType, CranelispError, ErrorLocation, MonoExpr, Span};

use crate::heap::{self, HeapAdt};

use super::FnCompiler;

fn canonical_payload<'a>(
    ty: &'a ConcreteType,
    head: &str,
    span: Span,
) -> Result<&'a ConcreteType, CranelispError> {
    match ty {
        ConcreteType::ADT(name, args)
            if name.module.as_ref() == "primitives"
                && name.name.as_ref() == head
                && args.len() == 1 =>
        {
            Ok(&args[0])
        }
        _ => Err(CranelispError::CodegenError {
            message: format!(
                "IO result-disposer carrier requires (primitives/{head} a), got {ty:?}"
            ),
            location: ErrorLocation::from_span(span),
        }),
    }
}

impl<'a, M: Module, C, L> FnCompiler<'a, M, C, L>
where
    C: cranelisp_types::CodeStore,
    L: cranelisp_types::LinkerStore,
{
    pub(crate) fn result_disposer_for_io_expr(
        &mut self,
        expr: &MonoExpr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let payload = canonical_payload(expr.ty(), "IO", span)?.clone();
        self.result_disposer_for_type(payload)
    }

    pub(crate) fn result_disposer_for_select_expr(
        &mut self,
        branches: &MonoExpr,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let branch = canonical_payload(branches.ty(), "Vec", span)?;
        let payload = canonical_payload(branch, "IO", span)?.clone();
        self.result_disposer_for_type(payload)
    }

    fn result_disposer_for_type(&mut self, payload: ConcreteType) -> Result<Value, CranelispError> {
        let Some(glue_id) =
            self.glue
                .request_if_owning(self.module, self.ctx.symbol_tables, payload)?
        else {
            return Ok(self.builder.ins().iconst(types::I64, 0));
        };
        let glue_ref = self.module.declare_func_in_func(glue_id, self.builder.func);
        Ok(self.builder.ins().func_addr(types::I64, glue_ref))
    }

    pub(crate) fn emit_bind_node(
        &mut self,
        inner: Value,
        continuation: Value,
        input_disposer: Value,
        span: Span,
    ) -> Result<Value, CranelispError> {
        let alloc_id = self
            .ctx
            .alloc_func_id
            .ok_or_else(|| CranelispError::CodegenError {
                message: "runtime/alloc not declared (need declare_intrinsics)".into(),
                location: ErrorLocation::from_span(span),
            })?;
        let node = heap::emit_alloc(
            &mut self.builder,
            self.module,
            alloc_id,
            HeapAdt::payload_size(3) as i64,
        );
        let tag = self.builder.ins().iconst(types::I64, 2);
        heap::heap_store(&mut self.builder, tag, node, HeapAdt::TAG_OFFSET);
        heap::heap_store(&mut self.builder, inner, node, HeapAdt::field_offset(0));
        heap::heap_store(
            &mut self.builder,
            continuation,
            node,
            HeapAdt::field_offset(1),
        );
        heap::heap_store(
            &mut self.builder,
            input_disposer,
            node,
            HeapAdt::field_offset(2),
        );
        Ok(node)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use cranelisp_types::{FQTypeName, ModuleFullPath, TypeName};

    fn adt(module: &str, name: &str, args: Vec<ConcreteType>) -> ConcreteType {
        ConcreteType::ADT(
            FQTypeName::new(ModuleFullPath::from(module), TypeName::from(name)),
            args,
        )
    }

    #[test]
    fn canonical_payload_accepts_only_the_exact_unary_primitives_head() {
        let canonical = adt("primitives", "IO", vec![ConcreteType::String]);
        assert_eq!(
            canonical_payload(&canonical, "IO", Span::SYNTHETIC).expect("canonical IO"),
            &ConcreteType::String
        );

        for malformed in [
            ConcreteType::Int,
            adt("user", "IO", vec![ConcreteType::String]),
            adt("primitives", "Vec", vec![ConcreteType::String]),
            adt("primitives", "IO", vec![]),
            adt(
                "primitives",
                "IO",
                vec![ConcreteType::String, ConcreteType::Int],
            ),
        ] {
            assert!(
                canonical_payload(&malformed, "IO", Span::SYNTHETIC).is_err(),
                "non-canonical carrier must be rejected: {malformed:?}"
            );
        }
    }
}

include!("../../declaration_macro.rs");

primitive_declarations! {
    user_extern {
        name: "missing-shim",
        metadata: (),
        type_vars: vec![],
        ownership: ()
    }
}

fn main() {}

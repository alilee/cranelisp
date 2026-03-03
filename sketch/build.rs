// Increase default main thread stack size to 64 MB.
// Prevents silent crash on deep mutual recursion (ROADMAP item D).
//
// cargo:rustc-link-arg-bins only applies the flag when linking binary targets,
// not proc-macro dylibs or cdylib platform DLLs.

fn main() {
    let target = std::env::var("CARGO_CFG_TARGET_OS").unwrap_or_default();
    let arch = std::env::var("CARGO_CFG_TARGET_ARCH").unwrap_or_default();

    match target.as_str() {
        "macos" => {
            // -stack_size is only valid for main executables on macOS/Darwin.
            println!("cargo:rustc-link-arg-bins=-Wl,-stack_size,0x4000000");
        }
        "linux" => {
            let _ = arch; // suppress unused warning
            println!("cargo:rustc-link-arg-bins=-Wl,-z,stacksize=67108864");
        }
        _ => {}
    }
}

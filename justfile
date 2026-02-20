# Build the project
build:
    cargo build

# Build all workspace members including platform DLLs
build-all:
    cargo build --workspace

# Build just the stdio platform DLL
build-stdio:
    cargo build -p cranelisp-stdio

# Run a cranelisp source file in batch mode
run file:
    cargo run -- --run {{file}}

# Run all tests (builds platform DLLs and exe bundle first — needed for integration and platform tests)
test:
    cargo build -p cranelisp-test-capture -p cranelisp-stdio -p cranelisp-exe-bundle
    cargo test --lib
    cargo test --test integration
    cargo test --test e2e
    cargo test --test rc -- --test-threads=1
    cargo test --test platform -- --test-threads=1

# Run platform DLL tests (requires DLLs to be built first)
test-platform:
    cargo build -p cranelisp-test-capture -p cranelisp-stdio
    cargo test --test platform -- --test-threads=1

# Run a specific example
hello:
    cargo run -- --run examples/hello.cl

factorial:
    cargo run -- --run examples/factorial.cl

list:
    cargo run -- --run examples/list.cl

vec:
    cargo run -- --run examples/vec.cl

# Build a standalone executable from a cranelisp source file
exe file:
    cargo build -p cranelisp-exe-bundle
    cargo run -- --exe {{file}}

# Check types and lints without building
check:
    cargo clippy

# Format source code
fmt:
    cargo fmt

# Cranelisp justfile — convenience recipes.

# Run an example program with the platform DLLs discoverable.
#
# Builds the platform cdylibs (stdio + test-capture) into target/debug, then
# runs the example with target/debug on the platform search path so the
# compiler resolves cargo's `libcranelisp_{name}.{ext}` artifacts directly
# (no symlinks, correct on every OS).
#
#   just run-example examples/21-hello-io.cl
run-example FILE:
    cargo build -p cranelisp-stdio -p cranelisp-test-capture
    CRANELISP_PLATFORM_PATH="{{justfile_directory()}}/target/debug" cargo run -- --run "{{FILE}}"

//! Language-internal builtin functions — re-exported from cranelisp-runtime,
//! plus the IO trampoline for deferred effect execution.

pub use cranelisp_runtime::intrinsics::*;

use cranelisp_platform::{IO_TAG_BIND, IO_TAG_EFFECT, IO_TAG_PAR, IO_TAG_PURE, IO_EFFECT_RESOURCE_OFFSET};

/// A cranelisp closure used as an IO continuation.
/// Layout: `[code_ptr: i64, captures...]`
/// Calling convention: `code_ptr(env_ptr, arg) -> IO task ptr`
struct Continuation(i64);

impl Continuation {
    /// Call this continuation with a value, returning a new IO task.
    fn call(self, val: i64) -> IoTask {
        unsafe {
            let code_ptr = *(self.0 as *const i64);
            let call: extern "C" fn(i64, i64) -> i64 =
                std::mem::transmute(code_ptr as *const ());
            IoTask(call(self.0, val))
        }
    }
}

/// FFI entry point: force an IO task tree to completion.
/// Called by the standalone exe startup stub.
#[unsafe(no_mangle)]
pub extern "C" fn cranelisp_run_io(io_ptr: i64) -> i64 {
    unsafe { IoTask::from_raw(io_ptr) }.run()
}

/// Execute Par branches with resource-token-aware scheduling.
///
/// Branches with resource_token=0 (unrestricted) each run independently in the
/// rayon thread pool. Branches with the same non-zero token are grouped and run
/// sequentially as a single rayon work item, serializing access to their resource.
/// Results are returned in original branch order.
fn execute_par_with_resource_ordering(ios: Vec<IoTask>) -> Vec<i64> {
    use rayon::prelude::*;
    use std::collections::HashMap;

    let count = ios.len();
    let mut results = vec![0i64; count];

    // Peek at each branch's resource token without consuming ownership.
    let tokens: Vec<i64> = ios.iter().map(|io| io.resource_token()).collect();

    // Group branch indices by token.
    // token=0 → each index gets its own singleton work item (fully independent).
    // non-zero token → all indices with the same token share one work item (sequential).
    let mut token_groups: HashMap<i64, Vec<usize>> = HashMap::new();
    let mut ungrouped_indices: Vec<usize> = Vec::new();

    for (i, &token) in tokens.iter().enumerate() {
        if token == 0 {
            ungrouped_indices.push(i);
        } else {
            token_groups.entry(token).or_default().push(i);
        }
    }

    // Take ownership of IoTasks by index into Option slots.
    let mut ios_opt: Vec<Option<IoTask>> = ios.into_iter().map(Some).collect();

    // Build work items: each is Vec<(original_index, IoTask)>, run sequentially.
    let mut work_items: Vec<Vec<(usize, IoTask)>> = Vec::new();

    for i in ungrouped_indices {
        work_items.push(vec![(i, ios_opt[i].take().unwrap())]);
    }
    for (_token, indices) in token_groups {
        let group: Vec<(usize, IoTask)> = indices
            .into_iter()
            .map(|i| (i, ios_opt[i].take().unwrap()))
            .collect();
        work_items.push(group);
    }

    // Execute all work items in parallel; within each item, run sequentially.
    let item_results: Vec<Vec<(usize, i64)>> = work_items
        .into_par_iter()
        .map(|group| group.into_iter().map(|(i, io)| (i, io.run())).collect())
        .collect();

    // Scatter results back to their original positions.
    for group_results in item_results {
        for (i, val) in group_results {
            results[i] = val;
        }
    }

    results
}

/// Opaque IO task tree pointer. Tags: Pure=0, Effect=1, Bind=2.
///
/// Created by `Pure`/`Effect` constructors and the `bind` primitive.
/// Interpreted by the trampoline via `run()`.
#[repr(transparent)]
pub struct IoTask(i64);

impl IoTask {
    /// Wrap a raw IO tree pointer.
    ///
    /// # Safety
    /// `ptr` must point to a valid IO task tree node (Pure/Effect/Bind).
    pub unsafe fn from_raw(ptr: i64) -> Self {
        IoTask(ptr)
    }

    fn tag(&self) -> i64 {
        unsafe { *(self.0 as *const i64) }
    }

    fn pure_val(&self) -> i64 {
        unsafe { *((self.0 as *const i64).add(1)) }
    }

    fn run_effect(&self) -> i64 {
        let thunk_ptr = unsafe { *((self.0 as *const i64).add(1)) };
        unsafe { cranelisp_platform::call_effect_thunk(thunk_ptr) }
    }

    fn split_bind(self) -> (IoTask, Continuation) {
        unsafe {
            let inner = *((self.0 as *const i64).add(1));
            let cont = *((self.0 as *const i64).add(2));
            (IoTask(inner), Continuation(cont))
        }
    }

    fn par_count(&self) -> usize {
        unsafe { *((self.0 as *const i64).add(1)) as usize }
    }

    fn par_ios(&self) -> Vec<IoTask> {
        let count = self.par_count();
        (0..count)
            .map(|i| IoTask(unsafe { *((self.0 as *const i64).add(2 + i)) }))
            .collect()
    }

    /// Read the resource token from an Effect node (0 = unrestricted).
    /// Returns 0 for non-Effect nodes — treated as unrestricted.
    fn resource_token(&self) -> i64 {
        if self.tag() == IO_TAG_EFFECT {
            unsafe { *((self.0 + IO_EFFECT_RESOURCE_OFFSET) as *const i64) }
        } else {
            0
        }
    }

    /// Force this IO task tree to completion via trampoline.
    ///
    /// Walks the deferred computation tree, executing effects and applying
    /// continuations. Uses an explicit continuation stack for O(1) call depth.
    pub fn run(self) -> i64 {
        let mut cont_stack: Vec<Continuation> = Vec::new();
        let mut current = self;

        loop {
            match current.tag() {
                IO_TAG_PURE => {
                    let val = current.pure_val();
                    match cont_stack.pop() {
                        Some(cont) => current = cont.call(val),
                        None => return val,
                    }
                }
                IO_TAG_EFFECT => {
                    let result = current.run_effect();
                    match cont_stack.pop() {
                        Some(cont) => current = cont.call(result),
                        None => return result,
                    }
                }
                IO_TAG_BIND => {
                    let (inner, cont) = current.split_bind();
                    cont_stack.push(cont);
                    current = inner;
                }
                IO_TAG_PAR => {
                    let ios = current.par_ios();
                    let count = ios.len();

                    // Group branches by resource token.
                    // token=0 → unrestricted; same non-zero token → must be sequential.
                    // Build: (original_index, io_task) pairs grouped by token.
                    // Strategy: for each unique non-zero token, run its group sequentially
                    // as a single rayon work item. Token-0 branches each run independently.
                    let results = execute_par_with_resource_ordering(ios);

                    // Allocate results array
                    let results_ptr =
                        cranelisp_runtime::intrinsics::alloc_with_rc(count * 8) as i64;
                    for (i, &val) in results.iter().enumerate() {
                        unsafe {
                            *((results_ptr as *mut i64).add(i)) = val;
                        }
                    }

                    // Pop continuation and call with results array
                    match cont_stack.pop() {
                        Some(cont) => current = cont.call(results_ptr),
                        None => return results_ptr,
                    }
                }
                tag => panic!("run_io_task: unknown IO tag {}", tag),
            }
        }
    }
}

# Failed batch-member attribution — retired record

Owner: `design` (backend). Status: **retired.** The contract, its rejected
alternatives and its unit scenarios are
[compile-to-module.md §15](compile-to-module.md#15-failure-attribution). This
file keeps the anchors the committed tests cite. Delete it when they move.

## 5. Unit scenarios

### 5.1 Required multi-name failure

A later member failing after an earlier success is attributed to the later
member, with its original cause and source location (compile-to-module §15).

### 5.2 Controls

Reversed names, a single-name failure, an unattributed non-body error, the
success control and unchanged live GOT values (compile-to-module §15).

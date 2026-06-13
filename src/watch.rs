// File watcher for the REPL: detects source file changes via OS notifications.
//
// Uses the `notify` crate with `RecommendedWatcher` (FSEvents on macOS,
// inotify on Linux). Watches parent directories of loaded `.cl` files
// for reliable editor detection (atomic rename pattern).
//
// Per repl/spec.md §14: non-blocking poll before each prompt, content hash
// comparison to skip metadata-only changes, cascade invalidation for
// dependents, last-known-good error recovery.

use std::collections::{HashMap, HashSet};
use std::path::{Path, PathBuf};
use std::sync::mpsc;

use notify::{Config, Event, EventKind, RecommendedWatcher, RecursiveMode, Watcher};

/// Filesystem watcher for REPL source file change detection.
///
/// Watches parent directories of loaded `.cl` files. Polls for changes
/// before each REPL prompt via non-blocking `try_recv`. Uses content
/// hashing (SHA-256) to skip metadata-only changes per repl/spec.md §14.
pub struct FileWatcher {
    watcher: RecommendedWatcher,
    rx: mpsc::Receiver<notify::Result<Event>>,
    watched_dirs: HashSet<PathBuf>,
    /// Content hashes of watched files. Used to detect actual content changes
    /// vs. metadata-only events (e.g., `touch foo.cl`). Keys are canonical paths.
    content_hashes: HashMap<PathBuf, String>,
}

impl FileWatcher {
    /// Create a new file watcher. Returns None if watcher initialization fails
    /// (e.g., OS notification API unavailable).
    pub fn new() -> Option<Self> {
        let (tx, rx) = mpsc::channel();
        let watcher = RecommendedWatcher::new(
            move |res| {
                let _ = tx.send(res);
            },
            Config::default(),
        )
        .ok()?;

        Some(FileWatcher {
            watcher,
            rx,
            watched_dirs: HashSet::new(),
            content_hashes: HashMap::new(),
        })
    }

    /// Watch the parent directory of a source file path.
    ///
    /// Watches at directory level (not individual files) for reliable editor
    /// detection — many editors save via atomic rename which would lose
    /// file-level watches.
    ///
    /// Records the initial content hash only on first encounter. Subsequent
    /// calls for the same file skip the hash update to avoid racing with
    /// `poll_changes` — if `sync_watcher` re-reads a file that was modified
    /// externally, it would silently overwrite the stored hash, making the
    /// change invisible to the next poll.
    pub fn watch_file(&mut self, path: &Path) {
        let dir = match path.parent() {
            Some(d) if !d.as_os_str().is_empty() => d,
            _ => return,
        };

        // Record the initial content hash only if we haven't seen this file yet.
        if let Ok(canonical) = path.canonicalize() {
            if !self.content_hashes.contains_key(&canonical) {
                if let Ok(content) = std::fs::read_to_string(&canonical) {
                    let hash = cranelisp_backend::cache::manifest::hash_source(&content);
                    self.content_hashes.insert(canonical, hash);
                }
            }
        }

        if self.watched_dirs.contains(dir) {
            return;
        }
        if self
            .watcher
            .watch(dir, RecursiveMode::NonRecursive)
            .is_ok()
        {
            self.watched_dirs.insert(dir.to_path_buf());
        }
    }

    /// Non-blocking poll for changed `.cl` files.
    ///
    /// Drains all queued events in one pass. Returns `None` if no changes,
    /// `Some(paths)` with the set of changed `.cl` file paths otherwise.
    /// Skips `.cl.tmp` files to avoid spurious events during atomic saves.
    ///
    /// Per repl/spec.md §14 and design review B-2: reads the file and computes
    /// its SHA-256 hash, comparing against the stored hash. Only reports changes
    /// where the content actually differs (skips metadata-only events).
    pub fn poll_changes(&mut self) -> Option<Vec<PathBuf>> {
        let mut candidates = HashSet::new();
        while let Ok(event_result) = self.rx.try_recv() {
            if let Ok(event) = event_result {
                match event.kind {
                    EventKind::Create(_) | EventKind::Modify(_) => {
                        for path in event.paths {
                            // Only .cl files, skip .cl.tmp (atomic save intermediates).
                            if path.extension() == Some(std::ffi::OsStr::new("cl"))
                                && !path
                                    .to_str()
                                    .is_some_and(|s| s.ends_with(".cl.tmp"))
                            {
                                let canonical = path.canonicalize().unwrap_or(path);
                                candidates.insert(canonical);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        // Filter candidates by content hash comparison.
        let mut changed = Vec::new();
        for path in candidates {
            if self.has_content_changed(&path) {
                changed.push(path);
            }
        }

        if changed.is_empty() {
            None
        } else {
            Some(changed)
        }
    }

    /// Check whether a file's content has actually changed since last seen.
    ///
    /// Reads the file and computes SHA-256. If the hash differs from the stored
    /// hash (or no hash was stored), returns true and updates the stored hash.
    /// If the file cannot be read (deleted between event and check), returns false.
    fn has_content_changed(&mut self, path: &Path) -> bool {
        let content = match std::fs::read_to_string(path) {
            Ok(c) => c,
            Err(_) => return false, // File gone (deleted or in-flight); skip.
        };
        let new_hash = cranelisp_backend::cache::manifest::hash_source(&content);

        match self.content_hashes.get(path) {
            Some(old_hash) if old_hash == &new_hash => false, // Same content; skip.
            _ => {
                // Content changed (or first time seeing this file).
                self.content_hashes.insert(path.to_path_buf(), new_hash);
                true
            }
        }
    }

    /// Update the stored content hash for a file without triggering a reload.
    ///
    /// Used by session persistence: after saving `user.cl`, we update the
    /// hash so the file watcher's next poll sees the saved content as
    /// "already known" and skips it.
    pub fn update_content_hash(&mut self, canonical_path: PathBuf, hash: String) {
        self.content_hashes.insert(canonical_path, hash);
    }

    /// Clear all watched directories and reset the watcher.
    ///
    /// Used during `/reset` to avoid stale watches for modules that
    /// no longer exist in the session (per /arch I-3).
    pub fn clear_all(&mut self) {
        for dir in self.watched_dirs.drain() {
            let _ = self.watcher.unwatch(&dir);
        }
        self.content_hashes.clear();
        // Drain any pending events.
        while self.rx.try_recv().is_ok() {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    // ══════════════════════════════════════════════════════════════════════
    // Harvest from tests/legacy/sprint23.rs (FIXME 0144, S81 W-E /dev int).
    //
    // sprint23.rs's watch cluster is filesystem+subprocess (e2e), carried
    // forward into tests/repl_watch.rs. The int-internal residue is the
    // content-hash change-detection invariant (repl/spec.md §14): a
    // metadata-only change (mtime touch, identical content rewrite) must NOT
    // be reported as a change, and `update_content_hash` must suppress the
    // self-write. Those are pure `FileWatcher` Rust-API properties — harvested
    // here adjacent to the code under test. (`FileWatcher::new()` may return
    // None if the OS notification API is unavailable in the sandbox; the
    // tests no-op cleanly in that case.)
    // ══════════════════════════════════════════════════════════════════════

    // spec: repl/spec.md §14 — content hashing skips metadata-only changes:
    //       rewriting a file with IDENTICAL content (mtime moves, bytes don't)
    //       MUST NOT be reported as a change; a real content change MUST be.
    #[test]
    fn harvest_content_hash_skips_identical_rewrite_reports_real_change() {
        let Some(mut w) = FileWatcher::new() else {
            return; // notify API unavailable in this environment — skip.
        };
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("m.cl");
        std::fs::write(&path, "(defn f [] 1)\n").expect("seed");
        let canonical = path.canonicalize().expect("canonicalize");

        // First encounter records the baseline hash.
        w.watch_file(&path);

        // Identical-content rewrite (mtime advances, content does not) — must
        // NOT count as a change.
        std::fs::write(&path, "(defn f [] 1)\n").expect("rewrite identical");
        assert!(
            !w.has_content_changed(&canonical),
            "identical-content rewrite (metadata-only) MUST NOT be reported as a change"
        );

        // A genuine content change MUST be reported.
        std::fs::write(&path, "(defn f [] 2)\n").expect("rewrite changed");
        assert!(
            w.has_content_changed(&canonical),
            "a real content change MUST be reported"
        );

        // After reporting, the new hash is stored: re-checking the same content
        // is now a no-op.
        assert!(
            !w.has_content_changed(&canonical),
            "after a reported change, the updated hash makes a re-check a no-op"
        );
    }

    // spec: repl/spec.md §14 + design/int/session-persistence.md §4 —
    //       `update_content_hash` records the post-save hash so the watcher's
    //       next poll treats the session's OWN write as already-known and does
    //       not report it (self-write suppression).
    #[test]
    fn harvest_update_content_hash_suppresses_self_write() {
        let Some(mut w) = FileWatcher::new() else {
            return;
        };
        let dir = tempfile::tempdir().expect("temp dir");
        let path = dir.path().join("user.cl");
        let content = "(defn g [] 42)\n";
        std::fs::write(&path, content).expect("write self-saved file");
        let canonical = path.canonicalize().expect("canonicalize");

        // Simulate session persistence: compute + register the saved hash.
        let hash = cranelisp_backend::cache::manifest::hash_source(content);
        w.update_content_hash(canonical.clone(), hash);

        // The watcher's change check now sees the self-write as already-known.
        assert!(
            !w.has_content_changed(&canonical),
            "a session self-write whose hash was registered MUST NOT be reported \
             as an external change"
        );
    }
}

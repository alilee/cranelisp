// File watcher for the REPL: detects source file changes via OS notifications.
//
// Uses the `notify` crate with `RecommendedWatcher` (FSEvents on macOS,
// inotify on Linux). Watches parent directories of loaded `.cl` files
// for reliable editor detection (atomic rename pattern).
//
// Per repl/spec.md §14: non-blocking poll before each prompt, and content
// state comparison to skip metadata-only changes.

use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::mpsc;

use notify::{Config, Event, EventKind, RecommendedWatcher, RecursiveMode, Watcher};

/// The session's record of each loaded source file's state, keyed by canonical
/// path: `SharedState.recorded_sources`.
pub(crate) type RecordedSources = dashmap::DashMap<PathBuf, FileState>;

/// Filesystem watcher for REPL source file change detection.
///
/// Watches parent directories of loaded `.cl` files and polls for changes via
/// non-blocking `try_recv`. It keeps no baseline of its own: a candidate is
/// changed when its state on disk differs from the session's record of what it
/// last loaded or wrote (`design/int/repl-lifecycle.md` §1.2, Content hash).
pub struct FileWatcher {
    watcher: RecommendedWatcher,
    rx: mpsc::Receiver<notify::Result<Event>>,
    watched_dirs: HashSet<PathBuf>,
    /// Every file this watcher has been asked to watch, by canonical path.
    seen: HashSet<PathBuf>,
    /// Files watched for the first time since the last poll. A save that
    /// landed between the session's read and the directory watch queued no
    /// event, so the next poll compares each of them with the record.
    first_sight: HashSet<PathBuf>,
}

/// The state of a source file (`design/int/repl-lifecycle.md` §1.2, Content
/// hash): its source hash, or that it exists but cannot be read.
#[derive(Debug, Clone, PartialEq, Eq)]
pub(crate) enum FileState {
    Source(String),
    Unreadable,
}

impl FileState {
    /// The state of a file whose content is `source`.
    pub(crate) fn of_source(source: &str) -> Self {
        FileState::Source(cranelisp_backend::cache::manifest::hash_source(source))
    }

    /// The state a read result implies; `None` when the file does not exist.
    pub(crate) fn of_read(read: &std::io::Result<String>) -> Option<Self> {
        match read {
            Ok(content) => Some(FileState::of_source(content)),
            Err(error) if error.kind() == std::io::ErrorKind::NotFound => None,
            Err(_) => Some(FileState::Unreadable),
        }
    }
}

/// The state of `path` now; `None` when it does not exist, which is never a
/// change: a delete, or the moment between an editor's write and rename.
fn observe(path: &Path) -> Option<FileState> {
    FileState::of_read(&std::fs::read_to_string(path))
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
            seen: HashSet::new(),
            first_sight: HashSet::new(),
        })
    }

    /// Watch the parent directory of a source file path.
    ///
    /// Watches at directory level (not individual files) for reliable editor
    /// detection — many editors save via atomic rename which would lose
    /// file-level watches. Records no state: a file seen for the first time
    /// is only queued for comparison with the session's record at the next
    /// poll.
    pub fn watch_file(&mut self, path: &Path) {
        let dir = match path.parent() {
            Some(d) if !d.as_os_str().is_empty() => d,
            _ => return,
        };
        if let Ok(canonical) = path.canonicalize()
            && self.seen.insert(canonical.clone())
        {
            self.first_sight.insert(canonical);
        }
        if self.watched_dirs.contains(dir) {
            return;
        }
        if self.watcher.watch(dir, RecursiveMode::NonRecursive).is_ok() {
            self.watched_dirs.insert(dir.to_path_buf());
        }
    }

    /// Non-blocking poll for changed `.cl` files.
    ///
    /// Drains all queued events in one pass, adds the files first seen since
    /// the last poll, and returns those whose state on disk differs from
    /// `recorded`, or `None` when there are none. Skips `.cl.tmp` files to
    /// avoid spurious events during atomic saves. The poll never updates the
    /// record: the reload's own read does.
    pub(crate) fn poll_changes(&mut self, recorded: &RecordedSources) -> Option<Vec<PathBuf>> {
        let mut candidates: HashSet<PathBuf> = std::mem::take(&mut self.first_sight);
        while let Ok(event_result) = self.rx.try_recv() {
            if let Ok(event) = event_result {
                match event.kind {
                    EventKind::Create(_) | EventKind::Modify(_) => {
                        for path in event.paths {
                            // Only .cl files, skip .cl.tmp (atomic save intermediates).
                            if path.extension() == Some(std::ffi::OsStr::new("cl"))
                                && !path.to_str().is_some_and(|s| s.ends_with(".cl.tmp"))
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

        let changed: Vec<PathBuf> = candidates
            .into_iter()
            .filter(|path| Self::has_content_changed(path, recorded))
            .collect();
        (!changed.is_empty()).then_some(changed)
    }

    /// Whether `path`'s state on disk differs from its recorded state. A file
    /// never recorded was never loaded, and a missing file keeps its
    /// generation: neither is a change (`design/int/repl-lifecycle.md` §1.2,
    /// Content hash).
    fn has_content_changed(path: &Path, recorded: &RecordedSources) -> bool {
        let (Some(state), Some(record)) = (observe(path), recorded.get(path)) else {
            return false;
        };
        state != *record
    }

    /// Clear all watched directories and reset the watcher.
    ///
    /// Used during `/reset` to avoid stale watches for modules that
    /// no longer exist in the session (per /arch I-3).
    pub fn clear_all(&mut self) {
        for dir in self.watched_dirs.drain() {
            let _ = self.watcher.unwatch(&dir);
        }
        self.seen.clear();
        self.first_sight.clear();
        // Drain any pending events.
        while self.rx.try_recv().is_ok() {}
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /// Bytes that are not UTF-8, so the file exists but cannot be read.
    const UNREADABLE: &[u8] = b"(defn f [] \xff)\n";

    /// A file `name` in `dir` holding `content`, and its canonical path.
    fn seeded(dir: &Path, name: &str, content: &[u8]) -> PathBuf {
        let path = dir.join(name);
        std::fs::write(&path, content).expect("seed");
        path.canonicalize().expect("canonicalize")
    }

    /// Record `path` as the session would after reading it now.
    fn record_now(recorded: &RecordedSources, path: &Path) {
        if let Some(state) = observe(path) {
            recorded.insert(path.to_path_buf(), state);
        }
    }

    // spec: repl/spec/14-file-watching.md §14.2; design/int/repl-lifecycle.md
    // §1.2 (Content hash), §1.3.2 (Watcher state) — against the record, a
    // same-content rewrite is no change and a real change is, every time until
    // the record is updated: the poll does not update it.
    #[test]
    fn harvest_content_hash_skips_identical_rewrite_reports_real_change() {
        let dir = tempfile::tempdir().expect("temp dir");
        let path = seeded(dir.path(), "m.cl", b"(defn f [] 1)\n");
        let recorded = RecordedSources::new();
        record_now(&recorded, &path);

        std::fs::write(&path, "(defn f [] 1)\n").expect("identical rewrite");
        assert!(
            !FileWatcher::has_content_changed(&path, &recorded),
            "same content"
        );
        std::fs::write(&path, "(defn f [] 2)\n").expect("real change");
        assert!(
            FileWatcher::has_content_changed(&path, &recorded),
            "a real change"
        );
        assert!(
            FileWatcher::has_content_changed(&path, &recorded),
            "still a change: only the reload's read updates the record"
        );
    }

    // spec: design/int/repl-lifecycle.md §1.2 (Content hash), §1.3.2 (Watcher
    // state, R1) — a file recorded unreadable at its load, then written
    // readable, is a change, also when `watch_file` runs before the poll.
    #[test]
    fn unreadable_at_first_watch_then_readable_is_a_change() {
        let Some(mut w) = FileWatcher::new() else {
            return;
        };
        let dir = tempfile::tempdir().expect("temp dir");
        let path = seeded(dir.path(), "user.cl", UNREADABLE);
        let recorded = RecordedSources::new();
        record_now(&recorded, &path);
        assert_eq!(
            recorded.get(&path).map(|s| s.clone()),
            Some(FileState::Unreadable)
        );

        std::fs::write(&path, "(defn f [] 5)\n").expect("readable save");
        w.watch_file(&path);
        assert_eq!(w.poll_changes(&recorded), Some(vec![path]));
    }

    // spec: design/int/repl-lifecycle.md §1.2 (Content hash), §1.3.2 (Watcher
    // state, R3) — a recorded file rewritten unreadable is a change; once the
    // rebuild records unreadable a second unreadable event is not; a deleted
    // file is not a change; a file never recorded is not a change.
    #[test]
    fn unreadable_save_is_a_change_once_and_a_deleted_file_is_none() {
        let dir = tempfile::tempdir().expect("temp dir");
        let path = seeded(dir.path(), "user.cl", b"(defn f [] 1)\n");
        let recorded = RecordedSources::new();
        record_now(&recorded, &path);

        std::fs::write(&path, UNREADABLE).expect("unreadable save");
        assert!(
            FileWatcher::has_content_changed(&path, &recorded),
            "an unreadable save is a change"
        );
        record_now(&recorded, &path);
        std::fs::write(&path, UNREADABLE).expect("unreadable again");
        assert!(
            !FileWatcher::has_content_changed(&path, &recorded),
            "a repeated unreadable state is not"
        );

        std::fs::remove_file(&path).expect("delete");
        assert!(
            !FileWatcher::has_content_changed(&path, &recorded),
            "a deleted file is not a change"
        );

        let other = seeded(dir.path(), "other.cl", b"(defn o [] 1)\n");
        assert!(
            !FileWatcher::has_content_changed(&other, &recorded),
            "a file never loaded is not a change"
        );
    }

    // spec: repl/spec/14-file-watching.md §14.2; design/int/repl-lifecycle.md
    // §1.2 (Content hash), §1.3.2 (One record) — the watcher keeps no
    // baseline: a file whose state changed before its first sight is a change
    // at the next poll, with no event queued for it; an unchanged file is not
    // reloaded at first sight.
    #[test]
    fn first_sight_compares_with_the_record_and_keeps_no_baseline() {
        let Some(mut w) = FileWatcher::new() else {
            return;
        };
        let dir = tempfile::tempdir().expect("temp dir");
        let saved = seeded(dir.path(), "saved.cl", b"(defn f [] 1)\n");
        let unchanged = seeded(dir.path(), "unchanged.cl", b"(defn u [] 1)\n");
        let recorded = RecordedSources::new();
        record_now(&recorded, &saved);
        record_now(&recorded, &unchanged);
        std::fs::write(&saved, "(defn f [] 1)\n(defn k [] 9)\n").expect("save");

        w.watch_file(&saved);
        w.watch_file(&unchanged);

        assert_eq!(w.poll_changes(&recorded), Some(vec![saved]));
    }
}

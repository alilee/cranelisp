use std::collections::HashSet;
use std::path::{Path, PathBuf};
use std::sync::mpsc;

use notify::{Config, Event, EventKind, RecommendedWatcher, RecursiveMode, Watcher};

pub struct FileWatcher {
    watcher: RecommendedWatcher,
    rx: mpsc::Receiver<notify::Result<Event>>,
    watched_dirs: HashSet<PathBuf>,
}

impl FileWatcher {
    /// Create a new file watcher. Returns None if watcher init fails.
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
        })
    }

    /// Watch the parent directory of a file path.
    /// Watches at directory level for reliable editor detection (atomic rename).
    pub fn watch_path(&mut self, path: &Path) {
        let dir = path.parent().unwrap_or(path);
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

    /// Non-blocking poll for changed .cl files.
    /// Returns None if no changes, Some(paths) if files changed.
    /// Callers use content hashing to determine whether a reload is needed.
    pub fn poll_changes(&mut self) -> Option<Vec<PathBuf>> {
        let mut changed = HashSet::new();
        while let Ok(event_result) = self.rx.try_recv() {
            if let Ok(event) = event_result {
                match event.kind {
                    EventKind::Create(_) | EventKind::Modify(_) => {
                        for path in event.paths {
                            // Only .cl files, skip .cl.tmp
                            if path.extension() == Some(std::ffi::OsStr::new("cl"))
                                && !path
                                    .to_str()
                                    .is_some_and(|s| s.ends_with(".cl.tmp"))
                            {
                                let canonical = path.canonicalize().unwrap_or(path);
                                changed.insert(canonical);
                            }
                        }
                    }
                    _ => {}
                }
            }
        }

        if changed.is_empty() {
            None
        } else {
            Some(changed.into_iter().collect())
        }
    }
}

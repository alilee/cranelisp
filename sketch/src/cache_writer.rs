//! Background cache writer for REPL responsiveness.
//!
//! Receives `CacheWritePacket`s via an mpsc channel, processes them
//! on a background thread (compile .o + write files), and writes
//! accumulated manifests on shutdown.

use std::path::PathBuf;
use std::sync::mpsc;
use std::thread::JoinHandle;

use crate::cache::{self, CacheWritePacket};
use crate::names::ModuleFullPath;

enum CacheWriteMsg {
    Write(CacheWritePacket),
    Shutdown,
}

/// Background cache writer. Processes cache write packets on a dedicated thread
/// so the REPL returns immediately after JIT compilation.
pub struct CacheWriter {
    tx: mpsc::Sender<CacheWriteMsg>,
    handle: Option<JoinHandle<()>>,
}

impl CacheWriter {
    /// Spawn a background cache writer thread.
    pub fn new() -> Self {
        let (tx, rx) = mpsc::channel::<CacheWriteMsg>();

        let handle = std::thread::Builder::new()
            .name("cache-writer".to_string())
            .spawn(move || {
                Self::run_loop(rx);
            })
            .expect("failed to spawn cache writer thread");

        CacheWriter {
            tx,
            handle: Some(handle),
        }
    }

    /// Submit a cache write packet for background processing.
    /// Non-blocking from the caller's perspective.
    pub fn submit(&self, packet: CacheWritePacket) {
        let _ = self.tx.send(CacheWriteMsg::Write(packet));
    }

    /// Shutdown the background thread, writing final manifests.
    /// Blocks until all pending writes complete.
    pub fn shutdown(&mut self) {
        let _ = self.tx.send(CacheWriteMsg::Shutdown);
        if let Some(handle) = self.handle.take() {
            let _ = handle.join();
        }
    }

    fn run_loop(rx: mpsc::Receiver<CacheWriteMsg>) {
        // Accumulate completed writes for manifest updates
        let mut lib_entries: Vec<(PathBuf, ModuleFullPath, String)> = Vec::new();
        let mut project_entries: Vec<(PathBuf, ModuleFullPath, String)> = Vec::new();

        loop {
            match rx.recv() {
                Ok(CacheWriteMsg::Write(packet)) => {
                    let cache_dir = packet.cache_dir.clone();
                    let is_lib = packet.is_lib;
                    if let Some((mod_path, source_hash, _is_lib)) =
                        cache::process_cache_packet(&packet)
                    {
                        if is_lib {
                            lib_entries.push((cache_dir, mod_path, source_hash));
                        } else {
                            project_entries.push((cache_dir, mod_path, source_hash));
                        }
                    }
                }
                Ok(CacheWriteMsg::Shutdown) | Err(_) => {
                    break;
                }
            }
        }

        // Write manifests for all cache directories that had writes
        Self::write_accumulated_manifests(&project_entries, &lib_entries);
    }

    fn write_accumulated_manifests(
        project_entries: &[(PathBuf, ModuleFullPath, String)],
        lib_entries: &[(PathBuf, ModuleFullPath, String)],
    ) {
        let target_triple = cranelift_native::builder()
            .map(|b| b.triple().to_string())
            .unwrap_or_else(|_| "unknown".to_string());

        // Group entries by cache directory and upsert into manifests
        Self::write_entries_to_manifests(project_entries, &target_triple);
        Self::write_entries_to_manifests(lib_entries, &target_triple);
    }

    fn write_entries_to_manifests(
        entries: &[(PathBuf, ModuleFullPath, String)],
        target_triple: &str,
    ) {
        if entries.is_empty() {
            return;
        }

        // Group by cache_dir
        let mut by_dir: std::collections::HashMap<&PathBuf, Vec<(&ModuleFullPath, &String)>> =
            std::collections::HashMap::new();
        for (dir, mod_path, hash) in entries {
            by_dir.entry(dir).or_default().push((mod_path, hash));
        }

        for (cache_dir, modules) in by_dir {
            let mut manifest = cache::read_manifest(cache_dir)
                .filter(cache::is_manifest_compatible)
                .unwrap_or_else(|| cache::CacheManifest::new(target_triple));

            for (mod_path, source_hash) in modules {
                manifest.upsert_module(mod_path.clone(), source_hash.to_string());
            }

            if let Err(e) = cache::write_manifest(cache_dir, &manifest) {
                eprintln!("warning: failed to write cache manifest: {}", e);
            }
        }
    }
}

impl Drop for CacheWriter {
    fn drop(&mut self) {
        if self.handle.is_some() {
            self.shutdown();
        }
    }
}

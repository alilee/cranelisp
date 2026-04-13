// Background cache writer thread for .o + .meta.json generation.
//
// When `CodegenBehaviour::InMemoryAndObject` is active, stage 6b queues background
// .o writes via this writer so the pipeline is never blocked by cache I/O.
//
// See design/arch/pipeline-v2.md §16.12 for the full design.

use std::collections::HashMap;
use std::sync::mpsc;

use cranelisp_backend::cache::object::{CacheWritePacket, process_cache_packet};
use cranelisp_types::ModuleFullPath;

// ---------------------------------------------------------------------------
// Request type
// ---------------------------------------------------------------------------

/// A request to write a .o + .meta.json for a module.
struct CacheWriteRequest {
    /// Module being written. Used for supersession detection.
    module: ModuleFullPath,
    /// Monotonically increasing sequence number. Used to detect
    /// superseded requests (newer request for same module wins).
    seq: u64,
    /// The Send-safe packet containing all data needed to produce the .o.
    packet: CacheWritePacket,
}

/// Sentinel value to tell the writer thread to shut down.
#[allow(clippy::large_enum_variant)]
enum WriterMessage {
    Write(CacheWriteRequest),
    /// Flush: signal that all prior writes must complete before the
    /// sender proceeds. The sender blocks on the oneshot receiver.
    Flush(mpsc::Sender<()>),
    Shutdown,
}

// ---------------------------------------------------------------------------
// Handle (main-thread side)
// ---------------------------------------------------------------------------

/// Handle to the background cache writer thread.
/// Owned by CompilationSession. Created when cache_state is initialized.
///
/// See design/arch/pipeline-v2.md §16.12.
pub struct CacheWriterHandle {
    /// Channel sender for queueing write requests.
    sender: mpsc::Sender<WriterMessage>,
    /// Join handle for the writer thread. Joined on Drop.
    thread: Option<std::thread::JoinHandle<()>>,
    /// Session-wide monotonic sequence counter for supersession.
    next_seq: u64,
}

impl Default for CacheWriterHandle {
    fn default() -> Self {
        Self::new()
    }
}

impl CacheWriterHandle {
    /// Create a new background writer. Spawns the writer thread.
    pub fn new() -> Self {
        let (sender, receiver) = mpsc::channel::<WriterMessage>();

        let thread = std::thread::Builder::new()
            .name("cranelisp-cache-writer".into())
            .spawn(move || {
                writer_thread_main(receiver);
            })
            .expect("failed to spawn cache writer thread");

        CacheWriterHandle {
            sender,
            thread: Some(thread),
            next_seq: 0,
        }
    }

    /// Queue a .o + .meta.json write for a module. Non-blocking.
    /// Returns immediately. The packet is moved to the writer thread.
    pub fn queue_write(&mut self, module: ModuleFullPath, packet: CacheWritePacket) {
        let seq = self.next_seq;
        self.next_seq += 1;

        let request = CacheWriteRequest {
            module,
            seq,
            packet,
        };

        // If the receiver is gone (thread panicked), silently drop the request.
        // Cache writing is best-effort — a failed write just means the next
        // session will recompile instead of loading from cache.
        let _ = self.sender.send(WriterMessage::Write(request));
    }

    /// Block until all pending writes have completed.
    ///
    /// Called by:
    /// - `link_file_inner()` in main.rs to flush background writes before
    ///   collecting .o paths for the linker.
    /// - Session persistence (REPL save) to ensure the latest .o is on disk.
    pub fn flush(&self) {
        let (done_tx, done_rx) = mpsc::channel();
        if self.sender.send(WriterMessage::Flush(done_tx)).is_ok() {
            // Block until the writer thread signals completion.
            let _ = done_rx.recv();
        }
    }
}

impl Drop for CacheWriterHandle {
    fn drop(&mut self) {
        // Send a shutdown sentinel, then join the thread.
        let _ = self.sender.send(WriterMessage::Shutdown);
        if let Some(thread) = self.thread.take() {
            let _ = thread.join();
        }
    }
}

// ---------------------------------------------------------------------------
// Writer thread
// ---------------------------------------------------------------------------

/// Main loop for the background writer thread.
///
/// Drains the receiver, processes write requests, and handles supersession.
fn writer_thread_main(receiver: mpsc::Receiver<WriterMessage>) {
    // Track the latest sequence number seen per module for supersession.
    let mut latest_seq: HashMap<ModuleFullPath, u64> = HashMap::new();

    // Set nice priority (best-effort — failure is fine).
    crate::thread_util::set_nice_priority();

    loop {
        let msg = match receiver.recv() {
            Ok(msg) => msg,
            Err(_) => break, // Sender dropped — exit.
        };

        match msg {
            WriterMessage::Write(request) => {
                process_write_request(&mut latest_seq, request);
            }
            WriterMessage::Flush(done_tx) => {
                // Drain all pending writes before signaling completion.
                // Try to receive any remaining Write messages without blocking.
                while let Ok(pending) = receiver.try_recv() {
                    match pending {
                        WriterMessage::Write(request) => {
                            process_write_request(&mut latest_seq, request);
                        }
                        WriterMessage::Flush(inner_done_tx) => {
                            // Nested flush — signal immediately (queue is drained).
                            let _ = inner_done_tx.send(());
                        }
                        WriterMessage::Shutdown => {
                            let _ = done_tx.send(());
                            return;
                        }
                    }
                }
                let _ = done_tx.send(());
            }
            WriterMessage::Shutdown => break,
        }
    }
}

/// Process a single write request, respecting supersession.
fn process_write_request(
    latest_seq: &mut HashMap<ModuleFullPath, u64>,
    request: CacheWriteRequest,
) {
    // Supersession check: skip if a newer request for the same module exists.
    let current_latest = latest_seq.get(&request.module).copied().unwrap_or(0);
    if request.seq < current_latest {
        return; // Superseded — skip this older request.
    }
    latest_seq.insert(request.module.clone(), request.seq);

    // Process the packet (compile .o + write files).
    // Errors are logged but not propagated — cache writing is best-effort.
    // TODO: thread symbol_tables through to cache writer for proper DashMap access.
    let empty_tables = dashmap::DashMap::new();
    if let Err(e) = process_cache_packet(&request.packet, &empty_tables) {
        eprintln!(
            "cache writer: failed to write cache for {}: {}",
            request.module,
            e.message()
        );
    }
}

// ---------------------------------------------------------------------------
// Tests
// ---------------------------------------------------------------------------

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn cache_writer_handle_creates_and_drops() {
        // Verify the background thread starts and stops cleanly.
        let handle = CacheWriterHandle::new();
        drop(handle);
    }

    #[test]
    fn cache_writer_flush_completes_on_empty_queue() {
        let handle = CacheWriterHandle::new();
        handle.flush();
        drop(handle);
    }
}

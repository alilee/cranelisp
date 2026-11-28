mod helpers;
use helpers::e2e::{Cranelisp, Stage, binary_path};
use std::{
    collections::BTreeMap,
    fs,
    path::Path,
    process::{Command, Stdio},
    time::{Duration, Instant},
};

fn snapshot(root: &Path) -> BTreeMap<String, Vec<u8>> {
    fn walk(base: &Path, dir: &Path, files: &mut BTreeMap<String, Vec<u8>>) {
        if !dir.exists() {
            return;
        }
        for entry in fs::read_dir(dir).unwrap() {
            let path = entry.unwrap().path();
            if path.is_dir() {
                walk(base, &path, files);
            } else {
                files.insert(
                    path.strip_prefix(base)
                        .unwrap()
                        .to_string_lossy()
                        .into_owned(),
                    fs::read(path).unwrap(),
                );
            }
        }
    }
    let mut files = BTreeMap::new();
    walk(root, &root.join(".cranelisp-cache"), &mut files);
    files
}

fn contending_run(root: &Path) -> Result<(), String> {
    // The prompt precedes the owner's asynchronous object and manifest writes.
    let deadline = Instant::now() + Duration::from_secs(5);
    let mut previous = snapshot(root);
    let mut stable_since = Instant::now();
    let before = loop {
        std::thread::sleep(Duration::from_millis(20));
        let current = snapshot(root);
        if current != previous {
            stable_since = Instant::now();
            previous = current;
        }
        let user_published = previous.contains_key(".cranelisp-cache/user.o")
            && previous.contains_key(".cranelisp-cache/user.meta.json")
            && previous
                .get(".cranelisp-cache/manifest.json")
                .and_then(|bytes| serde_json::from_slice::<serde_json::Value>(bytes).ok())
                .is_some_and(|manifest| manifest["modules"].get("user").is_some());
        if user_published && stable_since.elapsed() >= Duration::from_millis(200) {
            break previous;
        }
        if Instant::now() >= deadline {
            return Err(format!(
                "owner cache did not settle with user object and manifest entry; files: {:?}",
                previous.keys().collect::<Vec<_>>()
            ));
        }
    };
    if before
        .keys()
        .any(|name| name.ends_with("/app.o") || name.ends_with("/lib.o"))
    {
        return Err("first owner must load neither app nor lib".into());
    }
    let mut child = Command::new(binary_path())
        .args(["--run", "app.cl"])
        .current_dir(root)
        .env("CRANELISP_LIB", root.join("lib"))
        .stdin(Stdio::null())
        .stdout(Stdio::null())
        .stderr(Stdio::piped())
        .spawn()
        .map_err(|e| e.to_string())?;
    let deadline = Instant::now() + Duration::from_secs(5);
    let status = loop {
        if let Some(status) = child.try_wait().map_err(|e| e.to_string())? {
            break status;
        }
        if Instant::now() >= deadline {
            let _ = child.kill();
            let _ = child.wait();
            return Err("cache-owner contender waited for the live owner".into());
        }
        std::thread::sleep(Duration::from_millis(10));
    };
    if status.code() != Some(41) {
        return Err(format!("contender must execute uncached, got {status}"));
    }
    let after = snapshot(root);
    let observation = if before == after {
        "unchanged".into()
    } else {
        let changed: std::collections::BTreeSet<_> = before
            .keys()
            .chain(after.keys())
            .filter(|name| before.get(*name) != after.get(*name))
            .cloned()
            .collect();
        format!("changed: {changed:?}")
    };
    fs::write(root.join("owner-observation"), observation).map_err(|e| e.to_string())?;
    Ok(())
}

fn project() -> Cranelisp {
    Cranelisp::new()
        .file("lib.cl", "(defn value [] 41)")
        .file(
            "app.cl",
            "(import [lib [value]]) (defn main [] (primitives/pure (value)))",
        )
        .user("(defn sentinel [] 0)\n")
}

// spec: design/int/int.md §7.7 — one live cache owner; contender executes without cache writes.
// defect: class=missing-runtime-check locus=src/cache.rs found=S125 owner=/dev
#[test]
fn s125_owner_contender_executes_without_mutating_cache_then_owner_releases() {
    // The manifest is flushed at shutdown; warm only the owner's user module.
    let warm = project().stdin("/quit\n").output().assert_ok();
    let first = warm
        .run_again()
        .staged_output(&[Stage::Observe(contending_run), Stage::Line("/quit")])
        .assert_ok();
    let observation = first.read_tmp("owner-observation");
    let unchanged = observation == "unchanged";
    let released = first.run_again().run("app.cl").output().assert_exit(41);
    assert!(
        released.tmp_exists(".cranelisp-cache/app.o"),
        "owner lock must end with its process"
    );
    assert!(
        unchanged,
        "contender changed cache bytes while the first owner was alive: {observation}"
    );
}

// spec: design/int/int.md §7.7 — an uncontended owner may publish app.o.
#[test]
fn s125_owner_uncontended_cache_control() {
    project()
        .run("app.cl")
        .output()
        .assert_exit(41)
        .tmp_exists(".cranelisp-cache/app.o")
        .then_some(())
        .expect("uncontended run writes app.o");
}

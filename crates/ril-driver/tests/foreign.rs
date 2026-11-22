#![forbid(unsafe_code)]

use std::{fs, path::PathBuf, process::Command};

use ril_driver::Driver;
use ril_test::{Unit, VirtualPackage, run_worker};

#[test]
fn aot_foreign_functions_support_first_class_calls_and_cleanup() {
    let temporary = tempfile::tempdir().unwrap();
    let source = temporary.path().join("host.c");
    let object = temporary.path().join("host.o");
    fs::write(
        &source,
        r#"
        #include <stdint.h>
        #include <stdio.h>
        extern uint64_t ril_rt_int_literal(void *context, const uint8_t *text, size_t length);
        static const uint64_t token = UINT64_C(0x800000000000ab00);
        uint64_t host_answer(void *context) {
            static const uint8_t digits[] = "18446744073709551616";
            return ril_rt_int_literal(context, digits, sizeof(digits) - 1);
        }
        uint64_t host_open(void *context) { (void)context; return token; }
        uint64_t host_live(void *context, uint64_t handle) {
            (void)context;
            return handle == token ? 2 : 1;
        }
        uint64_t host_close(void *context, uint64_t handle) {
            (void)context;
            if (handle == token) puts("closed");
            return 0;
        }
    "#,
    )
    .unwrap();
    let compiled = Command::new(std::env::var_os("CC").unwrap_or_else(|| "cc".into()))
        .args(["-c", "-o"])
        .arg(&object)
        .arg(&source)
        .output()
        .unwrap();
    assert!(
        compiled.status.success(),
        "{}",
        String::from_utf8_lossy(&compiled.stderr)
    );

    let mut package = VirtualPackage::new(Unit::Bin);
    package.insert(
        PathBuf::from("pkg/sys.d.ril"),
        br#"
        pub opaque type Handle use(host_close)
        pub let host_answer: int
        pub fn host_open() @io -> new Handle
        pub fn host_live(ref handle: Handle) @io -> bool
        pub fn host_close(new handle: Handle) @io -> ()
    "#
        .to_vec(),
    );
    package.insert(
        package.entry.clone(),
        br#"
        use pkg/sys
        fn main() @io -> () {
            use handle = Sys::host_open()
            let live = Sys::host_live
            assert(Sys::host_answer == 18446744073709551616 && live(ref handle))
            assert(String::inspect(ref handle) == "<Handle>")
            panic("foreign cleanup")
        }
    "#
        .to_vec(),
    );

    let executable = temporary
        .path()
        .join(format!("ril{}", std::env::consts::EXE_SUFFIX));
    Driver
        .compile_aot_with_links(&package, &executable, &[object])
        .unwrap();
    let output = run_worker(&mut Command::new(executable)).unwrap();
    assert_eq!(output.status.code(), Some(1));
    assert_eq!(output.stdout, b"closed\n");
    assert!(String::from_utf8_lossy(&output.stderr).contains("foreign cleanup"));
}

//! Versioned Ril sources. The compiler parses and checks these ordinary modules.
pub const VERSION: &str = env!("CARGO_PKG_VERSION");

pub struct Module {
    pub path: &'static str,
    pub namespace: &'static str,
    pub source: &'static str,
}

pub const MODULES: &[Module] = &[
    Module {
        path: "ril/_storage",
        namespace: "Storage",
        source: include_str!("../modules/storage.ril"),
    },
    Module {
        path: "ril/array",
        namespace: "Array",
        source: include_str!("../modules/array.ril"),
    },
    Module {
        path: "ril/bytes",
        namespace: "Bytes",
        source: include_str!("../modules/bytes.ril"),
    },
    Module {
        path: "ril/clock",
        namespace: "Clock",
        source: include_str!("../modules/clock.ril"),
    },
    Module {
        path: "ril/concurrent",
        namespace: "Concurrent",
        source: include_str!("../modules/concurrent.ril"),
    },
    Module {
        path: "ril/concurrent/channel",
        namespace: "Channel",
        source: include_str!("../modules/channel.ril"),
    },
    Module {
        path: "ril/crypto",
        namespace: "Crypto",
        source: include_str!("../modules/crypto.ril"),
    },
    Module {
        path: "ril/deque",
        namespace: "Deque",
        source: include_str!("../modules/deque.ril"),
    },
    Module {
        path: "ril/encoding/binary",
        namespace: "Binary",
        source: include_str!("../modules/binary.ril"),
    },
    Module {
        path: "ril/encoding/hex",
        namespace: "Hex",
        source: include_str!("../modules/hex.ril"),
    },
    Module {
        path: "ril/env",
        namespace: "Env",
        source: include_str!("../modules/env.ril"),
    },
    Module {
        path: "ril/file",
        namespace: "File",
        source: include_str!("../modules/file.ril"),
    },
    Module {
        path: "ril/heap",
        namespace: "Heap",
        source: include_str!("../modules/heap.ril"),
    },
    Module {
        path: "ril/io",
        namespace: "Io",
        source: include_str!("../modules/io.ril"),
    },
    Module {
        path: "ril/iter",
        namespace: "Iter",
        source: include_str!("../modules/iter.ril"),
    },
    Module {
        path: "ril/map",
        namespace: "Map",
        source: include_str!("../modules/map.ril"),
    },
    Module {
        path: "ril/math",
        namespace: "Math",
        source: include_str!("../modules/math.ril"),
    },
    Module {
        path: "ril/num",
        namespace: "Num",
        source: include_str!("../modules/num.ril"),
    },
    Module {
        path: "ril/option",
        namespace: "Options",
        source: include_str!("../modules/option.ril"),
    },
    Module {
        path: "ril/order",
        namespace: "Order",
        source: include_str!("../modules/order.ril"),
    },
    Module {
        path: "ril/os",
        namespace: "Os",
        source: include_str!("../modules/os.ril"),
    },
    Module {
        path: "ril/parallel",
        namespace: "Parallel",
        source: include_str!("../modules/parallel.ril"),
    },
    Module {
        path: "ril/path",
        namespace: "Path",
        source: include_str!("../modules/path.ril"),
    },
    Module {
        path: "ril/process",
        namespace: "Process",
        source: include_str!("../modules/process.ril"),
    },
    Module {
        path: "ril/random",
        namespace: "Random",
        source: include_str!("../modules/random.ril"),
    },
    Module {
        path: "ril/result",
        namespace: "Results",
        source: include_str!("../modules/result.ril"),
    },
    Module {
        path: "ril/set",
        namespace: "Set",
        source: include_str!("../modules/set.ril"),
    },
    Module {
        path: "ril/string",
        namespace: "String",
        source: include_str!("../modules/string.ril"),
    },
    Module {
        path: "ril/string_builder",
        namespace: "StringBuilder",
        source: include_str!("../modules/string_builder.ril"),
    },
    Module {
        path: "ril/test",
        namespace: "Test",
        source: include_str!("../modules/test.ril"),
    },
    Module {
        path: "ril/time",
        namespace: "Time",
        source: include_str!("../modules/time.ril"),
    },
    Module {
        path: "ril/unicode",
        namespace: "Unicode",
        source: include_str!("../modules/unicode.ril"),
    },
];

#!/usr/bin/env bash
# Reproducible end-to-end Ril compiler & runtime benchmark suite (Phase R6).
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$ROOT"

echo "Building release ril CLI..."
cargo build --release --locked -p ril-cli --bin ril >/dev/null
RIL="$ROOT/target/release/ril"

TMP="$(mktemp -d)"
trap 'rm -rf "$TMP"' EXIT

now_ns() {
    date +%s%N
}

run_bench() {
    local name="$1"
    local file="$2"
    local exe="$TMP/${name}.bin"
    local t0 t1 t2 c_ms r_ms
    t0="$(now_ns)"
    "$RIL" build --release "$file" -o "$exe"
    t1="$(now_ns)"
    "$exe" >/dev/null
    t2="$(now_ns)"
    c_ms="$(awk -v d="$((t1 - t0))" 'BEGIN { printf "%.2f", d / 1000000.0 }')"
    r_ms="$(awk -v d="$((t2 - t1))" 'BEGIN { printf "%.2f", d / 1000000.0 }')"
    printf "%-28s compile=%8sms  run=%8sms\n" "$name" "$c_ms" "$r_ms"
}

# 1. SmallInt tight arithmetic loop (1,000,000 iterations)
cat > "$TMP/smallint_loop.ril" <<'EOF'
fn main() -> () {
    var i = 0
    var acc = 0
    while i < 1000000 {
        acc = acc + (i & 7) - (i & 3)
        i = i + 1
    }
    assert(acc > 0)
}
EOF

# 2. Nested record allocation (100,000 allocations)
cat > "$TMP/alloc_records.ril" <<'EOF'
type Pair = .{ a: int, b: int }
fn main() -> () {
    var i = 0
    var sum = 0
    while i < 100000 {
        let p = Pair.{ a: i, b: i + 1 }
        sum = sum + p.a
        i = i + 1
    }
    assert(sum == 4999950000)
}
EOF

# 3. 10,000-entry Map insert & lookup (bisim-hashed IndexMap)
cat > "$TMP/map_10k.ril" <<'EOF'
fn main() -> () {
    let mut m: [int: int] = [:]
    var i = 0
    while i < 10000 {
        m[i] = i * 3 + 1
        i += 1
    }
    var total = 0
    var j = 0
    while j < 10000 {
        if let Some(v) = m?[j] {
            total += v
        }
        j += 1
    }
    assert(total == 149995000)
}
EOF

# 4. 9-parameter via MDD forwarding (check compile time)
cat > "$TMP/via_9param.ril" <<'EOF'
type Box = .{ var v: int }
fn forward9(
    via a: Box, via b: Box, via c: Box,
    via d: Box, via e: Box, via f: Box,
    via g: Box, via h: Box, via i: Box
) -> int {
    a.v + b.v + c.v + d.v + e.v + f.v + g.v + h.v + i.v
}
fn main() -> () {
    let x = Box.{ v: 1 }
    assert(forward9(x, x, x, x, x, x, x, x, x) == 9)
}
EOF

# 5. Structured concurrency: Fiber::map across 200 tasks
cat > "$TMP/fiber_map.ril" <<'EOF'
use ril/fiber
fn main() -> () {
    Fiber::run \-> {
        let mut xs: []int = []
        var i = 0
        while i < 200 {
            Array::push(mut xs, i)
            i += 1
        }
        let frozen = new xs
        let res = Fiber::map(frozen, \n -> {
            Fiber::yield_now()
            n * 2
        })
        assert(len(res) == 200 && res[199] == 398)
    }
}
EOF

echo "=== Ril Benchmark Suite (release -O2) ==="
run_bench "smallint_loop_1m" "$TMP/smallint_loop.ril"
run_bench "alloc_records_100k" "$TMP/alloc_records.ril"
run_bench "map_insert_lookup_10k" "$TMP/map_10k.ril"
run_bench "via_9param_mdd" "$TMP/via_9param.ril"
run_bench "fiber_map_200" "$TMP/fiber_map.ril"

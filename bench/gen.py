#!/usr/bin/env python3
"""Generate the micro-kernel workloads in bench/wat/.

Every kernel is one self-contained module exporting a zero-argument @run@ that returns an
i32 checksum. Zero arguments because wabt's `wasm-interp` cannot pass any, and a checksum
because agreeing on it across runtimes makes the benchmark a differential test as well.

Sizes are chosen so the current interpreter spends between a third of a second and a second
per kernel: long enough to swamp process start-up, short enough for a sweep to be quick.

  ./bench/gen.py        # rewrite bench/wat/*.wat
"""

from __future__ import annotations

from pathlib import Path

WAT = Path(__file__).resolve().parent / "wat"

# The index depths swept to expose the cost of a witness walk: `local.get`, `call` and a
# branch all carry a unary index (`Elem`/`Control` depth) that the interpreter walks.
DEPTHS = [2, 4, 16, 64]


def counted(body: str, *, iters: int, locals_: str = "", result: str = "local.get $acc", pre: str = "", extra: str = "") -> str:
    """A module whose `run` repeats `body` `iters` times, then returns `result`."""
    return f"""(module
{extra}  (func (export "run") (result i32)
    (local $i i32) (local $acc i32){locals_}
{pre}    block $done
      loop $next
        local.get $i
        i32.const {iters}
        i32.ge_u
        br_if $done
{body}
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $next
      end
    end
    {result}))
"""


def kernels() -> dict[str, str]:
    out: dict[str, str] = {}

    # The per-runtime start-up baseline: everything but the work.
    out["empty"] = '(module\n  (func (export "run") (result i32)\n    i32.const 0))\n'

    # Calls and branching: naive recursive Fibonacci, the classic call-bound kernel.
    out["fib"] = """(module
  (func $fib (param $n i32) (result i32)
    local.get $n
    i32.const 2
    i32.lt_u
    if (result i32)
      local.get $n
    else
      local.get $n
      i32.const 1
      i32.sub
      call $fib
      local.get $n
      i32.const 2
      i32.sub
      call $fib
      i32.add
    end)
  (func (export "run") (result i32)
    i32.const 30
    call $fib))
"""

    # Pure dispatch: a chain of i32 ALU operations, no calls and no memory.
    out["loop-arith"] = counted(
        """        local.get $acc
        local.get $i
        i32.add
        local.get $i
        i32.const 3
        i32.mul
        i32.xor
        local.get $i
        i32.const 7
        i32.and
        i32.shl
        i32.const 2654435761
        i32.mul
        local.get $acc
        i32.const 13
        i32.shr_u
        i32.or
        i32.const 1
        i32.sub
        local.set $acc""",
        iters=500_000,
    )

    # The same in i64, to separate the 64-bit paths from the 32-bit ones.
    out["loop-arith64"] = counted(
        """        local.get $acc64
        local.get $i
        i64.extend_i32_u
        i64.add
        local.get $i
        i64.extend_i32_u
        i64.const 3
        i64.mul
        i64.xor
        i64.const 2654435761
        i64.mul
        local.get $acc64
        i64.const 13
        i64.shr_u
        i64.or
        i64.const 1
        i64.sub
        local.set $acc64""",
        iters=500_000,
        locals_=" (local $acc64 i64)",
        result="local.get $acc64\n    i32.wrap_i64",
    )

    # Witness-walk sweeps. The hot local, callee and branch target sit at index `d`, so a
    # cost linear in `d` is the unary index being walked and nothing else.
    for d in DEPTHS:
        # $i is 0 and $acc is 1, so d-2 fillers put $hot at exactly index d.
        fillers = "".join(f" (local $pad{k} i32)" for k in range(d - 2))
        out[f"locals-{d}"] = counted(
            """        local.get $hot
        local.get $i
        i32.add
        local.set $hot""",
            iters=1_000_000,
            locals_=fillers + " (local $hot i32)",
            result="local.get $hot",
        )

        leaves = "".join(
            f"  (func $leaf{k} (param $x i32) (result i32)\n    local.get $x\n    i32.const {k + 1}\n    i32.add)\n"
            for k in range(d + 1)
        )
        out[f"funcs-{d}"] = counted(
            f"""        local.get $i
        call $leaf{d}
        local.get $acc
        i32.add
        local.set $acc""",
            iters=500_000,
            extra=leaves,
        )

        opens = "".join(f"        block $l{k}\n" for k in range(d))
        closes = "".join("        end\n" for _ in range(d))
        out[f"labels-{d}"] = counted(
            opens
            + """        local.get $acc
        local.get $i
        i32.add
        local.set $acc
        br $l0
"""
            + closes.rstrip("\n"),
            iters=500_000,
        )

        globals_ = "".join(f"  (global $g{k} (mut i32) (i32.const {k}))\n" for k in range(d + 1))
        out[f"globals-{d}"] = counted(
            f"""        global.get $g{d}
        local.get $i
        i32.add
        global.set $g{d}
        global.get $g{d}
        local.get $acc
        i32.xor
        local.set $acc""",
            iters=500_000,
            extra=globals_,
        )

    # Memory: a sequential sweep (store then load back, 1 MiB, always resident) …
    out["memory-stream"] = counted(
        """        local.get $i
        i32.const 2
        i32.shl
        i32.const 1048572
        i32.and
        local.set $addr
        local.get $addr
        local.get $i
        i32.store
        local.get $acc
        local.get $addr
        i32.load
        i32.add
        local.set $acc""",
        iters=1_000_000,
        locals_=" (local $addr i32)",
        extra="  (memory 16)\n",
    )

    # … and a scattered one. The prefill matters: our pages are allocated on write, so
    # reading untouched memory would measure the sparse representation, not a real load.
    out["memory-random"] = counted(
        """        local.get $x
        i32.const 1103515245
        i32.mul
        i32.const 12345
        i32.add
        local.set $x
        local.get $acc
        local.get $x
        i32.const 16
        i32.shr_u
        i32.const 262140
        i32.and
        i32.load
        i32.add
        local.set $acc""",
        iters=1_000_000,
        locals_=" (local $x i32)",
        extra="  (memory 16)\n",
        pre="""    block $filled
      loop $fill
        local.get $i
        i32.const 65536
        i32.ge_u
        br_if $filled
        local.get $i
        i32.const 2
        i32.shl
        local.get $i
        i32.store
        local.get $i
        i32.const 1
        i32.add
        local.set $i
        br $fill
      end
    end
    i32.const 0
    local.set $i
""",
    )

    out["call-indirect"] = counted(
        """        local.get $i
        local.get $i
        i32.const 3
        i32.and
        call_indirect (type $sig)
        local.get $acc
        i32.add
        local.set $acc""",
        iters=500_000,
        extra="""  (type $sig (func (param i32) (result i32)))
  (table 4 funcref)
  (elem (i32.const 0) $t0 $t1 $t2 $t3)
  (func $t0 (param $x i32) (result i32) local.get $x i32.const 1 i32.add)
  (func $t1 (param $x i32) (result i32) local.get $x i32.const 2 i32.mul)
  (func $t2 (param $x i32) (result i32) local.get $x i32.const 3 i32.xor)
  (func $t3 (param $x i32) (result i32) local.get $x i32.const 4 i32.sub)
""",
    )

    out["br-table"] = counted(
        """        block $out
          block $c3
            block $c2
              block $c1
                block $c0
                  local.get $i
                  i32.const 3
                  i32.and
                  br_table $c0 $c1 $c2 $c3 $c3
                end
                local.get $acc
                i32.const 1
                i32.add
                local.set $acc
                br $out
              end
              local.get $acc
              i32.const 2
              i32.add
              local.set $acc
              br $out
            end
            local.get $acc
            i32.const 3
            i32.add
            local.set $acc
            br $out
          end
          local.get $acc
          i32.const 5
          i32.add
          local.set $acc
        end""",
        iters=500_000,
    )

    out["float"] = counted(
        """        local.get $f
        f64.const 1.0000001
        f64.mul
        local.get $i
        f64.convert_i32_u
        f64.sqrt
        f64.add
        local.set $f""",
        iters=500_000,
        locals_=" (local $f f64)",
        result="local.get $f\n    i64.reinterpret_f64\n    i32.wrap_i64",
    )

    return out


def main() -> None:
    WAT.mkdir(parents=True, exist_ok=True)
    for stale in WAT.glob("*.wat"):
        stale.unlink()
    for name, text in sorted(kernels().items()):
        (WAT / f"{name}.wat").write_text(
            f";; {name} — generated by bench/gen.py; edit the generator, not this file.\n" + text
        )
    print(f"generated {len(kernels())} kernels in {WAT}")


if __name__ == "__main__":
    main()

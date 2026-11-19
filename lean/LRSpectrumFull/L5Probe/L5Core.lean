/-
# L5 kernel probe, core: the witness-line check of the five-speed route, on `Nat` only

Probe of the kernel speed of the planned certificate.  No Mathlib import: the
kernel cost is then measured without the 5.8 GB Mathlib baseline.  Link to the project's `ML` is in `L5Link`.

* `times`  (module L5Times): reduced fractions a/q, 1 ≤ a ≤ q/2, 5 ≤ q ≤ 60, ordered by q then a (548 entries).
* `okAt a q v`  : `q ≤ 5 * min r (q - r)` with `r = v * a % q`  (the distance of `v a / q` to `ℤ` is at least `1/5`).
* `witnessS v0 .. v4` : some time `a/q` of the list has `okAt` for all five speeds (early exit in both loops).
* `witnessP n` : the same on the packed tuple `n = v0 + 1024 v1 + 1024² v2 + 1024³ v3 + 1024⁴ v4`.
* `lcgLoop`, `sumOps`: instruments for the probe (enumeration without stored data; mod-op counter).

No `sorry`, no `native_decide`, no axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5Probe.L5Times

namespace L5

def okAt (a q v : Nat) : Bool := Nat.ble q (5 * Nat.min (v * a % q) (q - v * a % q))

def good (a q v0 v1 v2 v3 v4 : Nat) : Bool :=
  okAt a q v0 && okAt a q v1 && okAt a q v2 && okAt a q v3 && okAt a q v4

def witnessS (v0 v1 v2 v3 v4 : Nat) : Bool :=
  times.any (fun p => good p.1 p.2 v0 v1 v2 v3 v4)

def witnessP (n : Nat) : Bool :=
  witnessS (n % 1024) (n / 1024 % 1024) (n / 1048576 % 1024) (n / 1073741824 % 1024)
    (n / 1099511627776 % 1024)

/-- list literal of packed tuples -/
def chunkOK (L : List Nat) : Bool := L.all witnessP

/-- one blob holds `j` tuples of radix `2^50` -/
def blobOK : Nat → Nat → Bool
  | 0, _ => true
  | j + 1, b => witnessP (b % 1125899906842624) && blobOK j (b / 1125899906842624)

def blobsOK (B : Nat) (L : List Nat) : Bool := L.all (blobOK B)

/-! ### instruments -/

/-- number of mod-ops spent at one time (early exit), same convention as the Rust generator -/
def cntAt (a q v0 v1 v2 v3 v4 : Nat) : Nat :=
  if !okAt a q v0 then 1 else if !okAt a q v1 then 2 else if !okAt a q v2 then 3
  else if !okAt a q v3 then 4 else 5

def opsList (v0 v1 v2 v3 v4 : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | p :: ps =>
    if good p.1 p.2 v0 v1 v2 v3 v4 then cntAt p.1 p.2 v0 v1 v2 v3 v4
    else cntAt p.1 p.2 v0 v1 v2 v3 v4 + opsList v0 v1 v2 v3 v4 ps

def opsP (n : Nat) : Nat :=
  opsList (n % 1024) (n / 1024 % 1024) (n / 1048576 % 1024) (n / 1073741824 % 1024)
    (n / 1099511627776 % 1024) times

def sumOps (L : List Nat) : Nat := L.foldl (fun s n => s + opsP n) 0

/-- LCG enumeration without stored data: `n` tuples, count of the witnessed ones -/
def lcgStep (s : Nat) : Nat := (1664525 * s + 1013904223) % 4294967296
def spd (s : Nat) : Nat := 1 + s / 256 % 520

def lcgLoop : Nat → Nat → Nat → Nat
  | 0, _, c => c
  | n + 1, s, c =>
    let s1 := lcgStep s
    let s2 := lcgStep s1
    let s3 := lcgStep s2
    let s4 := lcgStep s3
    let s5 := lcgStep s4
    lcgLoop n s5 (c + if witnessS (spd s1) (spd s2) (spd s3) (spd s4) (spd s5) then 1 else 0)

end L5

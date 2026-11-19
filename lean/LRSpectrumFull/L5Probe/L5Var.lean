/-
# L5 probe: checker variants (kernel cost comparison).  No Mathlib.

* V1 : `Nat.ble` twice instead of `Nat.min` (no `Nat.min` unfolding), `List.any`/`List.all` as before.
* V2 : V1 with direct `List.rec` loops (no `brecOn` structure).
* V3 : V2 with the times grouped by q (`timesG`), inner loop over `a`.
* V4 : per-level 64-bit-slot mask table (`tablesM`): five `v % q` lookups by shift, four `land`, one test.
-/
import LRSpectrumFull.L5Probe.L5Core
import LRSpectrumFull.L5Probe.L5Tables

namespace L5

def ok2 (q r : Nat) : Bool := Nat.ble q (5 * r) && Nat.ble q (5 * (q - r))
def okB (a q v : Nat) : Bool := ok2 q (v * a % q)
def goodB (a q v0 v1 v2 v3 v4 : Nat) : Bool :=
  okB a q v0 && okB a q v1 && okB a q v2 && okB a q v3 && okB a q v4

/-- V1 -/
def wit1 (v0 v1 v2 v3 v4 : Nat) : Bool := times.any (fun p => goodB p.1 p.2 v0 v1 v2 v3 v4)
def dec (f : Nat → Nat → Nat → Nat → Nat → Bool) (n : Nat) : Bool :=
  f (n % 1024) (n / 1024 % 1024) (n / 1048576 % 1024) (n / 1073741824 % 1024) (n / 1099511627776 % 1024)
def chunk1 (L : List Nat) : Bool := L.all (dec wit1)

/-- V2 -/
noncomputable def wit2 (v0 v1 v2 v3 v4 : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => goodB p.1 p.2 v0 v1 v2 v3 v4 || ih) times
noncomputable def allR (f : Nat → Bool) (L : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun n _ ih => f n && ih) L
noncomputable def chunk2 (L : List Nat) : Bool := allR (dec wit2) L

/-- V3 -/
noncomputable def lvlAny (q v0 v1 v2 v3 v4 : Nat) (as : List Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false
    (fun a _ ih => (ok2 q (v0 * a % q) && ok2 q (v1 * a % q) && ok2 q (v2 * a % q) &&
      ok2 q (v3 * a % q) && ok2 q (v4 * a % q)) || ih) as
noncomputable def wit3 (v0 v1 v2 v3 v4 : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => lvlAny p.1 v0 v1 v2 v3 v4 p.2 || ih) timesG
noncomputable def chunk3 (L : List Nat) : Bool := allR (dec wit3) L

/-- V4 -/
def slot (T q v : Nat) : Nat := Nat.shiftRight T (64 * (v % q)) % 18446744073709551616
def lvlM (q T v0 v1 v2 v3 v4 : Nat) : Bool :=
  !(Nat.beq (Nat.land (Nat.land (Nat.land (Nat.land (slot T q v0) (slot T q v1)) (slot T q v2))
    (slot T q v3)) (slot T q v4)) 0)
noncomputable def wit4 (v0 v1 v2 v3 v4 : Nat) : Bool :=
  List.rec (motive := fun _ => Bool) false (fun p _ ih => lvlM p.1 p.2 v0 v1 v2 v3 v4 || ih) tablesM
noncomputable def chunk4 (L : List Nat) : Bool := allR (dec wit4) L

end L5

namespace L5

/-- V4 on blobs: `j` tuples of radix `2^50` per blob -/
noncomputable def blobOK4 (j b : Nat) : Bool :=
  Nat.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun _ ih b => dec wit4 (b % 1125899906842624) && ih (b / 1125899906842624)) j b
noncomputable def blobs4 (B : Nat) (L : List Nat) : Bool := allR (blobOK4 B) L

end L5

namespace L5

/-- LCG enumeration with the V4 (mask table) witness -/
noncomputable def lcgLoop4 : Nat → Nat → Nat → Nat
  | 0, _, c => c
  | n + 1, s, c =>
    let s1 := lcgStep s
    let s2 := lcgStep s1
    let s3 := lcgStep s2
    let s4 := lcgStep s3
    let s5 := lcgStep s4
    lcgLoop4 n s5 (c + if wit4 (spd s1) (spd s2) (spd s3) (spd s4) (spd s5) then 1 else 0)

end L5

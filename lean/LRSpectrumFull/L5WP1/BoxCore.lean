/-
# WP1 box theorem, kernel side: the per-tuple test and the enumeration loops (no Mathlib)

For five natural numbers `a < b < c < d < e` the test `tupleOK nt ex a b c d e` holds when one of

* the gcd of the five is not `1` (non-primitive tuples are reduced by scaling, see `BoxSound`),
* `wit4`: some time `x/q` of the fixed list of `L5Times` keeps all five runners at distance `>= 1/5` (mask-table checker V4),
* `exOK`: a recorded time `(x, q)` for the tuple works (the few tuples with `ML >= 1/5` but no time with `q <= 60`),
* `ntMem`: the tuple is on the near-tight list `nt` (its value is proved separately, `BoxNT`).

`pairLoop B nt ex a b` runs the test over all `b < c < d < e <= B`; `chunkP` runs a list of pairs `(a,b)`;
`allPairs B` is the list of all pairs that can start a tuple with maximum `<= B`.  Completeness of the enumeration is
proved in `BoxSound` (`master_of_chunks`); the data modules only supply chunk lists.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5Probe.L5Var

namespace L5W

open L5

def ntMem (nt : List (List Nat)) (a b c d e : Nat) : Bool := nt.any (fun l => l == [a, b, c, d, e])

def exOK (ex : List (List Nat × Nat × Nat)) (a b c d e : Nat) : Bool :=
  ex.any (fun r => r.1 == [a, b, c, d, e] && Nat.blt 0 r.2.2 && okAt r.2.1 r.2.2 a && okAt r.2.1 r.2.2 b &&
    okAt r.2.1 r.2.2 c && okAt r.2.1 r.2.2 d && okAt r.2.1 r.2.2 e)

noncomputable def tupleOK (nt : List (List Nat)) (ex : List (List Nat × Nat × Nat)) (a b c d e : Nat) : Bool :=
  !(Nat.beq (Nat.gcd (Nat.gcd (Nat.gcd (Nat.gcd a b) c) d) e) 1) || wit4 a b c d e || exOK ex a b c d e ||
    ntMem nt a b c d e

noncomputable def pairLoop (B : Nat) (nt : List (List Nat)) (ex : List (List Nat × Nat × Nat)) (a b : Nat) : Bool :=
  (List.range' (b + 1) (B - b)).all fun c =>
    (List.range' (c + 1) (B - c)).all fun d =>
      (List.range' (d + 1) (B - d)).all fun e => tupleOK nt ex a b c d e

noncomputable def chunkP (B : Nat) (nt : List (List Nat)) (ex : List (List Nat × Nat × Nat))
    (ps : List (Nat × Nat)) : Bool :=
  ps.all fun p => pairLoop B nt ex p.1 p.2

/-- all pairs `(a, b)` with `1 <= a < b <= B - 3` in lexicographic order -/
def allPairs (B : Nat) : List (Nat × Nat) :=
  (List.range' 1 (B - 4)).flatMap fun a => (List.range' (a + 1) (B - 3 - a)).map fun b => (a, b)

end L5W

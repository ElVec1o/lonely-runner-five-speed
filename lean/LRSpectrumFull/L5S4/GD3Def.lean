/-
# L5S4.GD3Def : flat-Int checker of the DEPTH-3 child step of one node (case-tree certificate, part 9, design (iii))

Node of `lib.rs::children` at `j = 2`, `d = 3` (t in Z^3).  Checker design (iii):

* the ball `bd * q(t) < bn * G` is certified per ROW `(t0, t1)` by an interval record `[lo, hi]` of `t2` (`rowOk`: the concave
  `F(t2) = bn G - bd q` is `> 0` at `lo, hi` and `<= 0` at `lo - 1, hi + 1`; an empty row stores its integer maximiser
  `m` as `lo = m, hi = m - 1` with `F(m) <= 0`, `F(m +- 1) <= F(m)`);
* the filters on the ball points are recomputed in the kernel on flat Ints: `gcdF3` (Nat.gcd), `eiF3`, `greedy3F` = the 3-D
  `exists_shorter` box search of `lib.rs::greedy_ok` for `j = 2` (Gram of `(l0, l1, y)`, bound `|l0|^2`) and the 2x2 test
  on the matrix `s` (`shortB`, S4F);
* a whole group `t0` is checked by `rowsOk`: consecutive `t1`, interval check, and ONE list equality
  `stored passes = filter passPoint (lo..hi)` per row.

`mode` selects how much of `cand` is evaluated (measurement instrument only): 0 ball, 1 + gcd, 2 + ei, 3 + 3-D box search,
4 + s-test (= full).  Only mode 4 is compared with the stored passes.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.CheckChildFilt

namespace LRSpectrumFull
namespace L5S4

structure FC3 where
  (p0 p1 p2 p3 p4 : ℤ)
  (q0 q1 q2 q3 q4 : ℤ)
  (b00 b01 b02 b03 b04 : ℤ)
  (b10 b11 b12 b13 b14 : ℤ)
  (b20 b21 b22 b23 b24 : ℤ)
  (r00 r01 r02 r03 r04 : ℤ)
  (r10 r11 r12 r13 r14 : ℤ)
  (r20 r21 r22 r23 r24 : ℤ)
  (a00 a01 a02 a11 a12 a22 : ℤ)
  (g bn bd T0 T1 T2 : ℤ)

/-- `lib.rs::rdiv` (positive divisor). -/
def rdv (a b : ℤ) : ℤ := (2 * a + b) / (2 * b)

abbrev Y5 := ℤ × ℤ × ℤ × ℤ × ℤ

/-- one reduction step `y := y - rdiv(y.l, l.l) * l`. -/
def redS (l0 l1 l2 l3 l4 : ℤ) (y : Y5) : Y5 :=
  let k := rdv (l0 * y.1 + l1 * y.2.1 + l2 * y.2.2.1 + l3 * y.2.2.2.1 + l4 * y.2.2.2.2)
    (l0 * l0 + l1 * l1 + l2 * l2 + l3 * l3 + l4 * l4)
  (y.1 - k * l0, y.2.1 - k * l1, y.2.2.1 - k * l2, y.2.2.2.1 - k * l3, y.2.2.2.2 - k * l4)

/-- `lib.rs::lift` for `j = 2`: `sum t_i r_i`, then `for _ in 0..2 { for i in (0..2).rev() reduce by l_i }`. -/
def lift3 (f : FC3) (t0 t1 t2 : ℤ) : Y5 :=
  let y : Y5 := (t0 * f.r00 + t1 * f.r10 + t2 * f.r20, t0 * f.r01 + t1 * f.r11 + t2 * f.r21,
    t0 * f.r02 + t1 * f.r12 + t2 * f.r22, t0 * f.r03 + t1 * f.r13 + t2 * f.r23, t0 * f.r04 + t1 * f.r14 + t2 * f.r24)
  let s1 := redS f.q0 f.q1 f.q2 f.q3 f.q4
  let s0 := redS f.p0 f.p1 f.p2 f.p3 f.p4
  s0 (s1 (s0 (s1 y)))

/-- 3-D box search of `exists_shorter(g, g00)` (Gram `[[g00,g01,g02],[g01,g11,g12],[g02,g12,g22]]`). -/
def short3 (g00 g01 g02 g11 g12 g22 : ℤ) : Bool :=
  let ad0 := g11 * g22 - g12 * g12
  let ad1 := g00 * g22 - g02 * g02
  let ad2 := g00 * g11 - g01 * g01
  let dt := g00 * ad0 - g01 * (g01 * g22 - g12 * g02) + g02 * (g01 * g12 - g11 * g02)
  let m0 := isqrtI ((max (g00 - 1) 0 * ad0) / dt)
  let m1 := isqrtI ((max (g00 - 1) 0 * ad1) / dt)
  let m2 := isqrtI ((max (g00 - 1) 0 * ad2) / dt)
  (rngI m0).any fun c0 => (rngI m1).any fun c1 => (rngI m2).any fun c2 =>
    (decide (c0 ≠ 0) || decide (c1 ≠ 0) || decide (c2 ≠ 0)) &&
    decide (g00 * c0 * c0 + g11 * c1 * c1 + g22 * c2 * c2 + 2 * (g01 * c0 * c1 + g02 * c0 * c2 + g12 * c1 * c2) < g00)

/-- `withS = false`: only the 3-D box search; `true`: also the 2x2 test on the matrix `s` (full `greedy_ok`, j = 2). -/
def greedy3G (withS : Bool) (f : FC3) (t0 t1 t2 : ℤ) : Bool :=
  let y := lift3 f t0 t1 t2
  let g00 := f.p0 * f.p0 + f.p1 * f.p1 + f.p2 * f.p2 + f.p3 * f.p3 + f.p4 * f.p4
  let g01 := f.p0 * f.q0 + f.p1 * f.q1 + f.p2 * f.q2 + f.p3 * f.q3 + f.p4 * f.q4
  let g11 := f.q0 * f.q0 + f.q1 * f.q1 + f.q2 * f.q2 + f.q3 * f.q3 + f.q4 * f.q4
  let g02 := f.p0 * y.1 + f.p1 * y.2.1 + f.p2 * y.2.2.1 + f.p3 * y.2.2.2.1 + f.p4 * y.2.2.2.2
  let g12 := f.q0 * y.1 + f.q1 * y.2.1 + f.q2 * y.2.2.1 + f.q3 * y.2.2.2.1 + f.q4 * y.2.2.2.2
  let g22 := y.1 * y.1 + y.2.1 * y.2.1 + y.2.2.1 * y.2.2.1 + y.2.2.2.1 * y.2.2.2.1 + y.2.2.2.2 * y.2.2.2.2
  short3 g00 g01 g02 g11 g12 g22 ||
    (withS && shortB (g00 * g11 - g01 * g01) (g00 * g12 - g01 * g02) (g00 * g22 - g02 * g02))

def greedy3F (f : FC3) (t0 t1 t2 : ℤ) : Bool := greedy3G true f t0 t1 t2

def gcdF3 (t0 t1 t2 : ℤ) : Bool := Nat.beq (Nat.gcd (Nat.gcd t0.natAbs t1.natAbs) t2.natAbs) 1

def eiAt3 (b0 b1 b2 t0 t1 t2 : ℤ) : Bool :=
  decide (b0 * t1 = b1 * t0) && decide (b0 * t2 = b2 * t0) && decide (b1 * t2 = b2 * t1)

def eiF3 (f : FC3) (t0 t1 t2 : ℤ) : Bool :=
  eiAt3 f.b00 f.b10 f.b20 t0 t1 t2 || eiAt3 f.b01 f.b11 f.b21 t0 t1 t2 || eiAt3 f.b02 f.b12 f.b22 t0 t1 t2 ||
  eiAt3 f.b03 f.b13 f.b23 t0 t1 t2 || eiAt3 f.b04 f.b14 f.b24 t0 t1 t2

/-- candidate filter, `mode` = number of stages evaluated (0 ball only .. 4 full); mode 3 = 3-D box search only. -/
def cand (mode : ℕ) (f : FC3) (t0 t1 t2 : ℤ) : Bool :=
  (decide (mode < 1) || gcdF3 t0 t1 t2) && (decide (mode < 2) || !eiF3 f t0 t1 t2) &&
  (decide (mode < 3) || !greedy3G (decide (4 ≤ mode)) f t0 t1 t2)

/-- full filter `children` at j = 2 after the radius test: gcd, ei, greedy. -/
def passPoint3 (f : FC3) (t0 t1 t2 : ℤ) : Bool := gcdF3 t0 t1 t2 && !eiF3 f t0 t1 t2 && !greedy3F f t0 t1 t2

def Fv (f : FC3) (t0 t1 t2 : ℤ) : ℤ :=
  f.bn * f.g - f.bd * (f.a00 * t0 * t0 + f.a11 * t1 * t1 + f.a22 * t2 * t2 +
    2 * (f.a01 * t0 * t1 + f.a02 * t0 * t2 + f.a12 * t1 * t2))

def rowOk (f : FC3) (t0 t1 lo hi : ℤ) : Bool :=
  if lo ≤ hi then
    decide (0 < Fv f t0 t1 lo) && decide (0 < Fv f t0 t1 hi) && decide (Fv f t0 t1 (hi + 1) ≤ 0) &&
    (if t0 = 0 ∧ t1 = 0 then decide (lo = 1) else decide (Fv f t0 t1 (lo - 1) ≤ 0))
  else
    decide (hi + 1 = lo) && decide (Fv f t0 t1 lo ≤ 0) && decide (Fv f t0 t1 (lo - 1) ≤ Fv f t0 t1 lo) &&
    decide (Fv f t0 t1 (lo + 1) ≤ Fv f t0 t1 lo)

def ptsList (lo hi : ℤ) : List ℤ := (List.range (hi + 1 - lo).toNat).map fun k : ℕ => lo + (k : ℤ)

/-- the passing `t2` of a row. -/
def passRow (f : FC3) (t0 t1 lo hi : ℤ) : List ℤ := (ptsList lo hi).filter fun t2 => passPoint3 f t0 t1 t2

/-- measurement instrument: number of points of a row surviving the first `mode` stages. -/
def cntRow (mode : ℕ) (f : FC3) (t0 t1 lo hi : ℤ) : ℕ := ((ptsList lo hi).filter fun t2 => cand mode f t0 t1 t2).length

/-- one group `t0`: `n` rows with consecutive `t1 = t1s, ...`, records `[t1, lo, hi, np, passes..]`; `mode = 4`: full comparison. -/
def rowsOk (f : FC3) (t0 : ℤ) : ℕ → ℤ → List ℤ → Bool
  | 0, _, data => data.isEmpty
  | n + 1, t1, t1' :: lo :: hi :: np :: rest =>
      decide (t1' = t1) && rowOk f t0 t1 lo hi && decide (rest.take np.toNat = passRow f t0 t1 lo hi) &&
        rowsOk f t0 n (t1 + 1) (rest.drop np.toNat)
  | _ + 1, _, _ => false

/-- measurement: rows only (no point evaluation at all). -/
def rowsOnly (f : FC3) (t0 : ℤ) : ℕ → ℤ → List ℤ → Bool
  | 0, _, data => data.isEmpty
  | n + 1, t1, t1' :: lo :: hi :: np :: rest =>
      decide (t1' = t1) && rowOk f t0 t1 lo hi && rowsOnly f t0 n (t1 + 1) (rest.drop np.toNat)
  | _ + 1, _, _ => false

/-- measurement: rows plus the number of points surviving `mode` stages (forces evaluation). -/
def rowsCnt (mode : ℕ) (f : FC3) (t0 : ℤ) : ℕ → ℤ → List ℤ → ℕ
  | 0, _, _ => 0
  | n + 1, t1, t1' :: lo :: hi :: np :: rest => cntRow mode f t0 t1 lo hi + rowsCnt mode f t0 n (t1 + 1) (rest.drop np.toNat)
  | _ + 1, _, _ => 0

def nRows (f : FC3) (t0 : ℤ) : ℕ := if t0 = 0 then (f.T1 + 1).toNat else (2 * f.T1 + 1).toNat
def firstT1 (f : FC3) (t0 : ℤ) : ℤ := if t0 = 0 then 0 else - f.T1

/-- the whole node: keys `0..T0`, every group checked. -/
def nodeOk (f : FC3) (G : List (ℤ × List ℤ)) : Bool :=
  decide (G.map Prod.fst = (List.range (f.T0 + 1).toNat).map fun k : ℕ => (k : ℤ)) &&
  G.all fun g => rowsOk f g.1 (nRows f g.1) (firstT1 f g.1) g.2

def nodeOnly (f : FC3) (G : List (ℤ × List ℤ)) : Bool :=
  G.all fun g => rowsOnly f g.1 (nRows f g.1) (firstT1 f g.1) g.2

def nodeCnt (mode : ℕ) (f : FC3) (G : List (ℤ × List ℤ)) : ℕ :=
  (G.map fun g => rowsCnt mode f g.1 (nRows f g.1) (firstT1 f g.1) g.2).sum

end L5S4
end LRSpectrumFull

/-
# L5S4.LinRCore : the ROW-INTERVAL five-speed LINES checker `classLinesR` (stage S4 block 17; MATHLIB-FREE core)

Replaces the box scan of `LinCore.classLinesB` by a boundary certificate.  A class record `g` (accessor, 32-bit digits `dg N k`,
layout of `LinCore` with ONE range, `X` dropped and `Y` at digit 64):

  0 cid | 1-5 gp | 6-10 ge | 11-25 l (3x5) | 26-35 k (2x5, pair-reduced) | 36-45 q (2x5) | 46-60 p (3x5) | 61 nr (= 1) | 62 lo | 63 hi | 64 Y

and ONE natural `W` (the stream, least significant bits first):
  * the 11-bit hint of the point `(1, 0)`;
  * for `y = 1 .. Y`: four 16-bit fields `p, g1, g2, r` (bias `2^15`), then the 11-bit hints of the points
    `x = p+1 .. g1-1` and `x = g2+1 .. r-1` of that row, in this order.
A hint is `64 * t + q` (low 6 bits `q`): `q >= 5` the time `t/q`; `q = 0` the point is not primitive; `q = 1` entry `t` is zero;
`q = 2` the absolute values of the entries of pair `t` agree; `q = 3` the residual tuple `T5V[t]` is among the |entries|; `q = 4` the
point is outside the range.  With `z(x) = a x + b y` and `D = a c - b^2` one has `a n(x,y) = z^2 + D y^2`; a row is certified when
`z(p) <= 0`, `z(p)^2 > a hi - D y^2`, `z(r) >= 0`, `z(r)^2 > a hi - D y^2` (so `n > hi` for `x <= p` and for `x >= r`) and, when
`g1 <= g2`, `z(g1)^2` and `z(g2)^2 < a lo - D y^2` (so `n < lo` on `[g1, g2]`).  The points of the two walks are the rest.

Soundness (`classLinesR_sound`) is in `LinRSound.lean`.  No `sorry`, no `native_decide`, no new axiom.  Not registered.
-/
import LRSpectrumFull.L5S4.LinCore

namespace LRSpectrumFull
namespace L5S4
namespace Lin

/-- a signed 16-bit field of the stream (bias `2^15`) at bit offset `k`. -/
def dec16 (W k : Nat) : Int := Int.subNatNat (Nat.mod (Nat.shiftRight W k) 65536) 32768

/-- entry `i` of the line point `(x, y)`. -/
def entR (g : Nat → Int) (x y : Int) (i : Nat) : Int := x * g (26 + i) + y * g (31 + i)

/-- the time hint `t / q` (hot path: the five entries written out). -/
def timeR (g : Nat → Int) (x y : Int) (t q : Nat) : Bool :=
  tmB (x * g 26 + y * g 31).natAbs (x * g 27 + y * g 32).natAbs (x * g 28 + y * g 33).natAbs
    (x * g 29 + y * g 34).natAbs (x * g 30 + y * g 35).natAbs (t, q)

/-- hint kind 1: entry `t` (< 5) is zero. -/
def zeroAtR (g : Nat → Int) (x y : Int) (t : Nat) : Bool := decide (t < 5) && (entR g x y t == 0)

/-- pairs of entries. -/
def pairA (t : Nat) : Nat := [0, 0, 0, 0, 1, 1, 1, 2, 2, 3].getD t 0
def pairB (t : Nat) : Nat := [1, 2, 3, 4, 2, 3, 4, 3, 4, 4].getD t 0

/-- hint kind 2: the absolute values of the entries of pair `t` (< 10) agree. -/
def eqAbsR (g : Nat → Int) (x y : Int) (t : Nat) : Bool :=
  decide (t < 10) && ((entR g x y (pairA t)).natAbs == (entR g x y (pairB t)).natAbs)

/-- hint kind 3: every entry of the residual tuple `T5V[t]` (`t < 25`, explicit) is among the five |entries|. -/
def t5R (g : Nat → Int) (x y : Int) (t : Nat) : Bool :=
  decide (t < 25) && (T5V.getD t []).all fun e =>
    (entR g x y 0).natAbs == e || (entR g x y 1).natAbs == e || (entR g x y 2).natAbs == e ||
    (entR g x y 3).natAbs == e || (entR g x y 4).natAbs == e

/-- the check of ONE visited point `(x, y)` against its 11-bit hint `h`. -/
def ptR (g : Nat → Int) (a b c x y : Int) (h : Nat) : Bool :=
  if 5 ≤ h % 64 then timeR g x y (h / 64) (h % 64)
  else if h % 64 = 0 then Nat.gcd x.natAbs y.natAbs != 1
  else if h % 64 = 1 then zeroAtR g x y (h / 64)
  else if h % 64 = 2 then eqAbsR g x y (h / 64)
  else if h % 64 = 3 then t5R g x y (h / 64)
  else decide (a * x * x + 2 * b * x * y + c * y * y < g 62) || decide (g 63 < a * x * x + 2 * b * x * y + c * y * y)

/-- the boundary check of row `y`: `p, r` bound the in-range part, `[g1, g2]` is an in-row hole (empty if `g1 > g2`). -/
def rowChk (g : Nat → Int) (a b c y p g1 g2 r : Int) : Bool :=
  decide (a * p + b * y ≤ 0) &&
  decide (a * g 63 - (a * c - b * b) * y * y < (a * p + b * y) * (a * p + b * y)) &&
  decide (0 ≤ a * r + b * y) &&
  decide (a * g 63 - (a * c - b * b) * y * y < (a * r + b * y) * (a * r + b * y)) &&
  (decide (g2 < g1) ||
    (decide ((a * g1 + b * y) * (a * g1 + b * y) < a * g 62 - (a * c - b * b) * y * y) &&
     decide ((a * g2 + b * y) * (a * g2 + b * y) < a * g 62 - (a * c - b * b) * y * y)))

/-- the walk `x0, x0+1, ..., x0+cnt-1` of one row, one hint per point (fuel `cnt`). -/
def segOk (g : Nat → Int) (a b c y : Int) : Int → Nat → Nat → Bool
  | _, 0, _ => true
  | x0, cnt + 1, W => ptR g a b c x0 y (Nat.mod W 2048) && segOk g a b c y (x0 + 1) cnt (Nat.shiftRight W 11)

/-- the rows `y, y+1, ..., y+f-1` (fuel `f`) of the stream `W`. -/
def rowsOk (g : Nat → Int) (a b c : Int) : Nat → Nat → Nat → Bool
  | 0, _, _ => true
  | f + 1, y, W =>
    rowChk g a b c (y : Int) (dec16 W 0) (dec16 W 16) (dec16 W 32) (dec16 W 48) &&
    segOk g a b c (y : Int) (dec16 W 0 + 1) ((dec16 W 16 - 1 - dec16 W 0).toNat) (Nat.shiftRight W 64) &&
    segOk g a b c (y : Int) (dec16 W 32 + 1) ((dec16 W 48 - 1 - dec16 W 32).toNat)
      (Nat.shiftRight W (64 + 11 * (dec16 W 16 - 1 - dec16 W 0).toNat)) &&
    rowsOk g a b c f (y + 1)
      (Nat.shiftRight W (64 + 11 * ((dec16 W 16 - 1 - dec16 W 0).toNat + (dec16 W 48 - 1 - dec16 W 32).toNat)))

/-- the structural checks (identity `k^T q + p^T l = I`, `l k = 0`, `nr = 1`, `D > 0`, `Y >= 0`, `D (Y+1)^2 > a hi`). -/
def structR (g : Nat → Int) : Bool :=
  let a := dt g 26 26
  let b := dt g 26 31
  let c := dt g 31 31
  let D := a * c - b * b
  let Y := g 64
  (dt g 11 26 == 0) && (dt g 11 31 == 0) && (dt g 16 26 == 0) && (dt g 16 31 == 0) && (dt g 21 26 == 0) && (dt g 21 31 == 0) &&
  (List.range 5).all (fun i => (List.range 5).all fun j =>
    g (26 + i) * g (36 + j) + g (31 + i) * g (41 + j) + g (46 + i) * g (11 + j) + g (51 + i) * g (16 + j) +
      g (56 + i) * g (21 + j) == (if i = j then 1 else 0)) &&
  (g 61 == 1) && decide (0 < D) && decide (0 ≤ Y) && decide (g 63 * a < D * ((Y + 1) * (Y + 1)))

/-- the whole class check: structure, the point `(1, 0)`, and the `Y` rows. -/
def classLinesR (g : Nat → Int) (W : Nat) : Bool :=
  structR g &&
  ptR g (dt g 26 26) (dt g 26 31) (dt g 31 31) 1 0 (Nat.mod W 2048) &&
  rowsOk g (dt g 26 26) (dt g 26 31) (dt g 31 31) (g 64).toNat 1 (Nat.shiftRight W 11)

end Lin
end L5S4
end LRSpectrumFull

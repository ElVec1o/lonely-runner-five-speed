/-
# L5S4.LinCore : the flat five-speed LINES checker (stage S4 block 16; MATHLIB-FREE core)

`classLinesB g` checks ONE class record (accessor `g : ℕ → ℤ`, in the data the 32-bit digits `dg N k` of one natural per class;
layout of `lean5_data/FORMAT_NOTES.md` section 3 with `k` pair-reduced, `q` updated, and two appended digits `X Y`):

  0 cid | 1-5 gp | 6-10 ge | 11-25 l (3x5) | 26-35 k (2x5) | 36-45 q (2x5) | 46-60 p (3x5) | 61 nr | 62+2t, 63+2t range t | 62+2nr X | 63+2nr Y

It checks (all `Int`/`Nat` arithmetic, no Mathlib, so a data module that imports only this file has a small floor):
1. `l . k = 0` (6 dots) and `k^T q + p^T l = I` (25 equations): `u = k^T (q u)` for every `u` with `l u = 0`;
2. `nr >= 1`, every range `hi <= nmax` (`nmax` = last `hi`), `D = a c - b^2 > 0` with `a = k0.k0`, `b = k0.k1`, `c = k1.k1`,
   `X, Y >= 0`, `D (X+1)^2 > nmax c`, `D (Y+1)^2 > nmax a` (so `n = a x^2 + 2 b x y + c y^2 <= nmax` forces `|x| <= X`, `|y| <= Y`);
3. the loop `y = 0 .. Y`, `x = -X .. X` (`y = 0`: only `x = 1`): a point passes the guard (`n` in a range, `gcd(x,y) = 1`, all five
   entries of `u = x k0 + y k1` nonzero with pairwise distinct absolute values) only if it has a time `a/q` of `TL5` with
   `q <= 5 min(r_i, q - r_i)` for all five `r_i = (|u_i| a) mod q`, or `|u|` contains every entry of a stored residual tuple `T5V`.

Soundness (`classLinesB_sound`) is in `LinSound.lean`.  No `sorry`, no `native_decide`, no new axiom.  Not registered.
-/
import LRSpectrumFull.L5S4.LinTL

namespace LRSpectrumFull
namespace L5S4
namespace Lin

/-- digit `k` of `N` (32-bit digits, bias `2^31`). -/
def dg (N k : Nat) : Int := Int.subNatNat (Nat.mod (Nat.shiftRight N (Nat.mul 32 k)) 4294967296) 2147483648

/-- row dot product of two 5-blocks of the accessor. -/
def dt (g : Nat → Int) (o p : Nat) : Int :=
  g o * g p + g (o + 1) * g (p + 1) + g (o + 2) * g (p + 2) + g (o + 3) * g (p + 3) + g (o + 4) * g (p + 4)

/-- the time test on one entry: `s = |u_i|`, time `a/q`: `q <= 5 min(r, q-r)` with `r = (s a) mod q`. -/
def okN (s a q : Nat) : Bool := decide (q ≤ 5 * ((s * a) % q)) && decide (5 * ((s * a) % q) ≤ 4 * q)

def tmB (s0 s1 s2 s3 s4 : Nat) (p : Nat × Nat) : Bool :=
  okN s0 p.1 p.2 && okN s1 p.1 p.2 && okN s2 p.1 p.2 && okN s3 p.1 p.2 && okN s4 p.1 p.2

def witB (s0 s1 s2 s3 s4 : Nat) : Bool := TL5.any (tmB s0 s1 s2 s3 s4)

/-- a stored residual tuple (`T5`): every entry of `r` is among the five entries `s_i` (the `s_i` are pairwise distinct). -/
def t5B (s0 s1 s2 s3 s4 : Nat) : Bool :=
  T5V.any fun r => r.all fun e => s0 == e || s1 == e || s2 == e || s3 == e || s4 == e

def inRangeB (g : Nat → Int) (nr : Nat) (n : Int) : Bool :=
  (List.range nr).any fun j => decide (g (62 + 2 * j) ≤ n) && decide (n ≤ g (63 + 2 * j))

/-- the guard of the loop point `(x, y)`. -/
def guardB (g : Nat → Int) (nr : Nat) (a b c x y : Int) : Bool :=
  inRangeB g nr (a * x * x + 2 * b * x * y + c * y * y) &&
  (Nat.gcd x.natAbs y.natAbs == 1) &&
  (x * g 26 + y * g 31 != 0) && (x * g 27 + y * g 32 != 0) && (x * g 28 + y * g 33 != 0) &&
  (x * g 29 + y * g 34 != 0) && (x * g 30 + y * g 35 != 0) &&
  ((x * g 26 + y * g 31).natAbs != (x * g 27 + y * g 32).natAbs) &&
  ((x * g 26 + y * g 31).natAbs != (x * g 28 + y * g 33).natAbs) &&
  ((x * g 26 + y * g 31).natAbs != (x * g 29 + y * g 34).natAbs) &&
  ((x * g 26 + y * g 31).natAbs != (x * g 30 + y * g 35).natAbs) &&
  ((x * g 27 + y * g 32).natAbs != (x * g 28 + y * g 33).natAbs) &&
  ((x * g 27 + y * g 32).natAbs != (x * g 29 + y * g 34).natAbs) &&
  ((x * g 27 + y * g 32).natAbs != (x * g 30 + y * g 35).natAbs) &&
  ((x * g 28 + y * g 33).natAbs != (x * g 29 + y * g 34).natAbs) &&
  ((x * g 28 + y * g 33).natAbs != (x * g 30 + y * g 35).natAbs) &&
  ((x * g 29 + y * g 34).natAbs != (x * g 30 + y * g 35).natAbs)

/-- the witness part of the loop point `(x, y)`. -/
def pbB (g : Nat → Int) (x y : Int) : Bool :=
  witB (x * g 26 + y * g 31).natAbs (x * g 27 + y * g 32).natAbs (x * g 28 + y * g 33).natAbs
    (x * g 29 + y * g 34).natAbs (x * g 30 + y * g 35).natAbs ||
  t5B (x * g 26 + y * g 31).natAbs (x * g 27 + y * g 32).natAbs (x * g 28 + y * g 33).natAbs
    (x * g 29 + y * g 34).natAbs (x * g 30 + y * g 35).natAbs

def lineB (g : Nat → Int) (nr : Nat) (a b c x y : Int) : Bool := !guardB g nr a b c x y || pbB g x y

/-- the structural checks (items 1 and 2 of the header). -/
def structB (g : Nat → Int) : Bool :=
  let nr := (g 61).toNat
  let nmax := g (63 + 2 * (nr - 1))
  let a := dt g 26 26
  let b := dt g 26 31
  let c := dt g 31 31
  let D := a * c - b * b
  let X := g (62 + 2 * nr)
  let Y := g (63 + 2 * nr)
  (dt g 11 26 == 0) && (dt g 11 31 == 0) && (dt g 16 26 == 0) && (dt g 16 31 == 0) && (dt g 21 26 == 0) && (dt g 21 31 == 0) &&
  (List.range 5).all (fun i => (List.range 5).all fun j =>
    g (26 + i) * g (36 + j) + g (31 + i) * g (41 + j) + g (46 + i) * g (11 + j) + g (51 + i) * g (16 + j) +
      g (56 + i) * g (21 + j) == (if i = j then 1 else 0)) &&
  decide (1 ≤ nr) && (List.range nr).all (fun j => decide (g (63 + 2 * j) ≤ nmax)) &&
  decide (0 < D) && decide (0 ≤ X) && decide (0 ≤ Y) &&
  decide (nmax * c < D * ((X + 1) * (X + 1))) && decide (nmax * a < D * ((Y + 1) * (Y + 1)))

/-- the whole class check. -/
def classLinesB (g : Nat → Int) : Bool :=
  let nr := (g 61).toNat
  let a := dt g 26 26
  let b := dt g 26 31
  let c := dt g 31 31
  let X := g (62 + 2 * nr)
  let Y := g (63 + 2 * nr)
  structB g &&
  (List.range (Y.toNat + 1)).all fun yn =>
    if yn = 0 then lineB g nr a b c 1 0
    else (List.range (2 * X.toNat + 1)).all fun xi => lineB g nr a b c ((xi : Int) - X) (yn : Int)

end Lin
end L5S4
end LRSpectrumFull

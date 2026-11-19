/-
# L5S4.GRecN : COST PROTOTYPE of a flat record check on packed Nat records for node #4 (stage S4 block 7; no soundness bridge yet)

`recN` re-implements the Boolean content of `recOkB` (record facts `RecFacts` and class map `d2Ok`) with plain `Int`
arithmetic on the record list (`r.getD`), to measure what the flat style buys.  It is NOT used in any theorem about
`ChildPass`; the bridge `recN = true -> recOkB = true` is the remaining proof work (see the report).

No `sorry`, no `native_decide`, no axiom.  Not part of any proof chain.
-/
import LRSpectrumFull.L5S4.GFlat

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

set_option maxRecDepth 100000

/-- digit `k` of a packed record (16-bit digits, bias 32768; as `unpackRec`). -/
def dgI (n k : ℕ) : ℤ := (((n / 65536 ^ k) % 65536 : ℕ) : ℤ) - 32768

def flatN : List ℕ := ck4P.flatMap Prod.snd

def d5N (a0 a1 a2 a3 a4 b0 b1 b2 b3 b4 : ℤ) : ℤ := a0 * b0 + a1 * b1 + a2 * b2 + a3 * b3 + a4 * b4

def mm1N (x w : ℤ) : ℤ := min (x % w) (w - x % w)

def wm5N (x0 x1 x2 x3 x4 w : ℤ) : ℤ := min (min (min (min (mm1N x0 w) (mm1N x1 w)) (mm1N x2 w)) (mm1N x3 w)) (mm1N x4 w)

def sel5N (x0 x1 x2 x3 x4 : ℤ) (s : ℕ) : ℤ := match s with | 0 => x0 | 1 => x1 | 2 => x2 | 3 => x3 | _ => x4

def recFactsN (f : FC) (r : ℕ) : Bool :=
  let g (k : ℕ) : ℤ := dgI r k
  let t0 := g 0; let t1 := g 1; let t2 := g 2; let t3 := g 3
  let y0 := g 4; let y1 := g 5; let y2 := g 6; let y3 := g 7; let y4 := g 8
  decide (d5N f.b00 f.b01 f.b02 f.b03 f.b04 y0 y1 y2 y3 y4 = t0) &&
  decide (d5N f.b10 f.b11 f.b12 f.b13 f.b14 y0 y1 y2 y3 y4 = t1) &&
  decide (d5N f.b20 f.b21 f.b22 f.b23 f.b24 y0 y1 y2 y3 y4 = t2) &&
  decide (d5N f.b30 f.b31 f.b32 f.b33 f.b34 y0 y1 y2 y3 y4 = t3) &&
  gcdF t0 t1 t2 t3 &&
  decide (d5N (g 9) (g 10) (g 11) (g 12) (g 13) f.h0 f.h1 f.h2 f.h3 f.h4 = 0) &&
  decide (d5N (g 9) (g 10) (g 11) (g 12) (g 13) y0 y1 y2 y3 y4 = 0) &&
  decide (d5N (g 14) (g 15) (g 16) (g 17) (g 18) f.h0 f.h1 f.h2 f.h3 f.h4 = 0) &&
  decide (d5N (g 14) (g 15) (g 16) (g 17) (g 18) y0 y1 y2 y3 y4 = 0) &&
  decide (d5N (g 19) (g 20) (g 21) (g 22) (g 23) f.h0 f.h1 f.h2 f.h3 f.h4 = 0) &&
  decide (d5N (g 19) (g 20) (g 21) (g 22) (g 23) y0 y1 y2 y3 y4 = 0) &&
  decide (d5N (g 9) (g 10) (g 11) (g 12) (g 13) (g 24) (g 25) (g 26) (g 27) (g 28) = 1) &&
  decide (d5N (g 9) (g 10) (g 11) (g 12) (g 13) (g 29) (g 30) (g 31) (g 32) (g 33) = 0) &&
  decide (d5N (g 9) (g 10) (g 11) (g 12) (g 13) (g 34) (g 35) (g 36) (g 37) (g 38) = 0) &&
  decide (d5N (g 14) (g 15) (g 16) (g 17) (g 18) (g 24) (g 25) (g 26) (g 27) (g 28) = 0) &&
  decide (d5N (g 14) (g 15) (g 16) (g 17) (g 18) (g 29) (g 30) (g 31) (g 32) (g 33) = 1) &&
  decide (d5N (g 14) (g 15) (g 16) (g 17) (g 18) (g 34) (g 35) (g 36) (g 37) (g 38) = 0) &&
  decide (d5N (g 19) (g 20) (g 21) (g 22) (g 23) (g 24) (g 25) (g 26) (g 27) (g 28) = 0) &&
  decide (d5N (g 19) (g 20) (g 21) (g 22) (g 23) (g 29) (g 30) (g 31) (g 32) (g 33) = 0) &&
  decide (d5N (g 19) (g 20) (g 21) (g 22) (g 23) (g 34) (g 35) (g 36) (g 37) (g 38) = 1) &&
  decide (0 < g 44) &&
  decide (g 44 ∣ d5N f.h0 f.h1 f.h2 f.h3 f.h4 (g 39) (g 40) (g 41) (g 42) (g 43)) &&
  decide (g 44 ∣ d5N y0 y1 y2 y3 y4 (g 39) (g 40) (g 41) (g 42) (g 43)) &&
  decide (g 44 < 5 * wm5N (g 39) (g 40) (g 41) (g 42) (g 43) (g 44))

/-- class map: signed permutation `(σ, ε)` of the record, first row up to sign, `L_2` equal as a lattice (`U`, `U'`). -/
def recClassN (f : FC) (L : List ℕ) (r : ℕ) : Bool :=
  let g (k : ℕ) : ℤ := dgI r k
  let q := L.getD (g 45).toNat 0
  let z (k : ℕ) : ℤ := dgI q k
  let s0 := (g 46).toNat % 5; let s1 := (g 47).toNat % 5; let s2 := (g 48).toNat % 5
  let s3 := (g 49).toNat % 5; let s4 := (g 50).toNat % 5
  let e0 := g 51; let e1 := g 52; let e2 := g 53; let e3 := g 54; let e4 := g 55
  let u00 := g 56; let u01 := g 57; let u10 := g 58; let u11 := g 59
  let v00 := g 60; let v01 := g 61; let v10 := g 62; let v11 := g 63
  let hs := sel5N f.h0 f.h1 f.h2 f.h3 f.h4
  let ys := sel5N (g 4) (g 5) (g 6) (g 7) (g 8)
  let ps := sel5N (z 4) (z 5) (z 6) (z 7) (z 8)
  let a0 := e0 * hs s0; let a1 := e1 * hs s1; let a2 := e2 * hs s2; let a3 := e3 * hs s3; let a4 := e4 * hs s4
  let c0 := e0 * ys s0; let c1 := e1 * ys s1; let c2 := e2 * ys s2; let c3 := e3 * ys s3; let c4 := e4 * ys s4
  let _ := ps
  decide (s0 ≠ s1) && decide (s0 ≠ s2) && decide (s0 ≠ s3) && decide (s0 ≠ s4) && decide (s1 ≠ s2) &&
  decide (s1 ≠ s3) && decide (s1 ≠ s4) && decide (s2 ≠ s3) && decide (s2 ≠ s4) && decide (s3 ≠ s4) &&
  (decide (e0 = 1) || decide (e0 = -1)) && (decide (e1 = 1) || decide (e1 = -1)) && (decide (e2 = 1) || decide (e2 = -1)) &&
  (decide (e3 = 1) || decide (e3 = -1)) && (decide (e4 = 1) || decide (e4 = -1)) &&
  ((decide (a0 = f.h0) && decide (a1 = f.h1) && decide (a2 = f.h2) && decide (a3 = f.h3) && decide (a4 = f.h4)) ||
   (decide (a0 = -f.h0) && decide (a1 = -f.h1) && decide (a2 = -f.h2) && decide (a3 = -f.h3) && decide (a4 = -f.h4))) &&
  decide (a0 = u00 * f.h0 + u01 * z 4) && decide (a1 = u00 * f.h1 + u01 * z 5) && decide (a2 = u00 * f.h2 + u01 * z 6) &&
  decide (a3 = u00 * f.h3 + u01 * z 7) && decide (a4 = u00 * f.h4 + u01 * z 8) &&
  decide (c0 = u10 * f.h0 + u11 * z 4) && decide (c1 = u10 * f.h1 + u11 * z 5) && decide (c2 = u10 * f.h2 + u11 * z 6) &&
  decide (c3 = u10 * f.h3 + u11 * z 7) && decide (c4 = u10 * f.h4 + u11 * z 8) &&
  decide (f.h0 = v00 * a0 + v01 * c0) && decide (f.h1 = v00 * a1 + v01 * c1) && decide (f.h2 = v00 * a2 + v01 * c2) &&
  decide (f.h3 = v00 * a3 + v01 * c3) && decide (f.h4 = v00 * a4 + v01 * c4) &&
  decide (z 4 = v10 * a0 + v11 * c0) && decide (z 5 = v10 * a1 + v11 * c1) && decide (z 6 = v10 * a2 + v11 * c2) &&
  decide (z 7 = v10 * a3 + v11 * c3) && decide (z 8 = v10 * a4 + v11 * c4)

def recN (f : FC) (L : List ℕ) (r : ℕ) : Bool :=
  recFactsN f r && decide ((dgI r 45).toNat < L.length) && recClassN f L r

end L5S4
end LRSpectrumFull

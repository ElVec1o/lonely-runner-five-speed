/-
# L5S4.GD3S1 : soundness of the flat depth-3 child checker, part 1 (stage S4 block 10)

Node `n : NodeW 2 3` to the flat structure `FC3` of `GD3Def` (`FC3.ofNode`), and the first necessity facts of
`ChildPass n y -> passPoint3 ... = true`:

* `lift3_form`, `tvec_lift3` : the generator's lift `lift3` is `∑ t_k r_k + (integer combination of l0, l1)`, so it has the
  coordinates `t` (the checker never needs the representative the Rust loop picked);
* `Fv_eq` : the flat ball function `Fv` is `bn * det(a) - bd * qform` of the node;
* `gcdF3_of`, `eiF3_imp` : gcd and `e_i` filters.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3Def

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. The lift -/

def toV5 (y : Y5) : V5 := ![y.1, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2]

theorem redS_form (l0 l1 l2 l3 l4 : ℤ) (y : Y5) :
    ∃ k : ℤ, ∀ c, toV5 (redS l0 l1 l2 l3 l4 y) c = toV5 y c - k * ![l0, l1, l2, l3, l4] c := by
  refine ⟨rdv (l0 * y.1 + l1 * y.2.1 + l2 * y.2.2.1 + l3 * y.2.2.2.1 + l4 * y.2.2.2.2)
    (l0 * l0 + l1 * l1 + l2 * l2 + l3 * l3 + l4 * l4), fun c => ?_⟩
  fin_cases c <;> first | rfl | simp [redS, toV5]

theorem four_steps (p0 p1 p2 p3 p4 q0 q1 q2 q3 q4 : ℤ) (y : Y5) :
    ∃ a b : ℤ, ∀ c, toV5 (redS p0 p1 p2 p3 p4 (redS q0 q1 q2 q3 q4 (redS p0 p1 p2 p3 p4 (redS q0 q1 q2 q3 q4 y)))) c =
      toV5 y c - a * ![p0, p1, p2, p3, p4] c - b * ![q0, q1, q2, q3, q4] c := by
  obtain ⟨k1, e1⟩ := redS_form q0 q1 q2 q3 q4 y
  obtain ⟨k2, e2⟩ := redS_form p0 p1 p2 p3 p4 (redS q0 q1 q2 q3 q4 y)
  obtain ⟨k3, e3⟩ := redS_form q0 q1 q2 q3 q4 (redS p0 p1 p2 p3 p4 (redS q0 q1 q2 q3 q4 y))
  obtain ⟨k4, e4⟩ := redS_form p0 p1 p2 p3 p4 (redS q0 q1 q2 q3 q4 (redS p0 p1 p2 p3 p4 (redS q0 q1 q2 q3 q4 y)))
  refine ⟨k2 + k4, k1 + k3, fun c => ?_⟩
  rw [e4 c, e3 c, e2 c, e1 c]
  ring

def y0Of3 (f : FC3) (t0 t1 t2 : ℤ) : Y5 :=
  (t0 * f.r00 + t1 * f.r10 + t2 * f.r20, t0 * f.r01 + t1 * f.r11 + t2 * f.r21,
    t0 * f.r02 + t1 * f.r12 + t2 * f.r22, t0 * f.r03 + t1 * f.r13 + t2 * f.r23, t0 * f.r04 + t1 * f.r14 + t2 * f.r24)

theorem lift3_eq (f : FC3) (t0 t1 t2 : ℤ) :
    lift3 f t0 t1 t2 = redS f.p0 f.p1 f.p2 f.p3 f.p4 (redS f.q0 f.q1 f.q2 f.q3 f.q4
      (redS f.p0 f.p1 f.p2 f.p3 f.p4 (redS f.q0 f.q1 f.q2 f.q3 f.q4 (y0Of3 f t0 t1 t2)))) := rfl

theorem lift3_form (f : FC3) (t0 t1 t2 : ℤ) :
    ∃ a b : ℤ, ∀ c, toV5 (lift3 f t0 t1 t2) c =
      t0 * ![f.r00, f.r01, f.r02, f.r03, f.r04] c + t1 * ![f.r10, f.r11, f.r12, f.r13, f.r14] c +
      t2 * ![f.r20, f.r21, f.r22, f.r23, f.r24] c
      - a * ![f.p0, f.p1, f.p2, f.p3, f.p4] c - b * ![f.q0, f.q1, f.q2, f.q3, f.q4] c := by
  obtain ⟨a, b, h⟩ := four_steps f.p0 f.p1 f.p2 f.p3 f.p4 f.q0 f.q1 f.q2 f.q3 f.q4 (y0Of3 f t0 t1 t2)
  refine ⟨a, b, fun c => ?_⟩
  rw [lift3_eq, h c]
  fin_cases c <;> first | rfl | simp [toV5, y0Of3]

/-! ## 2. The flat structure of a node -/

/-- Gram entry of the `K` basis. -/
def gk (n : NodeW 2 3) (i j : Fin 3) : ℤ := dot (n.b i) (n.b j)

def FC3.ofNode (n : NodeW 2 3) (bn bd : ℤ) : FC3 where
  p0 := n.rows 0 0
  p1 := n.rows 0 1
  p2 := n.rows 0 2
  p3 := n.rows 0 3
  p4 := n.rows 0 4
  q0 := n.rows 1 0
  q1 := n.rows 1 1
  q2 := n.rows 1 2
  q3 := n.rows 1 3
  q4 := n.rows 1 4
  b00 := n.b 0 0
  b01 := n.b 0 1
  b02 := n.b 0 2
  b03 := n.b 0 3
  b04 := n.b 0 4
  b10 := n.b 1 0
  b11 := n.b 1 1
  b12 := n.b 1 2
  b13 := n.b 1 3
  b14 := n.b 1 4
  b20 := n.b 2 0
  b21 := n.b 2 1
  b22 := n.b 2 2
  b23 := n.b 2 3
  b24 := n.b 2 4
  r00 := n.r 0 0
  r01 := n.r 0 1
  r02 := n.r 0 2
  r03 := n.r 0 3
  r04 := n.r 0 4
  r10 := n.r 1 0
  r11 := n.r 1 1
  r12 := n.r 1 2
  r13 := n.r 1 3
  r14 := n.r 1 4
  r20 := n.r 2 0
  r21 := n.r 2 1
  r22 := n.r 2 2
  r23 := n.r 2 3
  r24 := n.r 2 4
  a00 := gk n 1 1 * gk n 2 2 - gk n 1 2 * gk n 1 2
  a01 := gk n 0 2 * gk n 1 2 - gk n 0 1 * gk n 2 2
  a02 := gk n 0 1 * gk n 1 2 - gk n 0 2 * gk n 1 1
  a11 := gk n 0 0 * gk n 2 2 - gk n 0 2 * gk n 0 2
  a12 := gk n 0 2 * gk n 0 1 - gk n 0 0 * gk n 1 2
  a22 := gk n 0 0 * gk n 1 1 - gk n 0 1 * gk n 0 1
  g := gk n 0 0 * (gk n 1 1 * gk n 2 2 - gk n 1 2 * gk n 1 2) +
    gk n 0 1 * (gk n 0 2 * gk n 1 2 - gk n 0 1 * gk n 2 2) + gk n 0 2 * (gk n 0 1 * gk n 1 2 - gk n 0 2 * gk n 1 1)
  bn := bn
  bd := bd
  T0 := isqrtI (bn * gk n 0 0 / bd)
  T1 := isqrtI (bn * gk n 1 1 / bd)
  T2 := isqrtI (bn * gk n 2 2 / bd)

theorem hN_zero (rows : Fin 4 → V5) : hN rows 0 = rows 0 := by simp [hN]
theorem hN_one (rows : Fin 4 → V5) : hN rows 1 = rows 1 := by simp [hN]

theorem Fv_eq (n : NodeW 2 3) (bn bd : ℤ) (y : V5) :
    Fv (FC3.ofNode n bn bd) (tvec n.b y 0) (tvec n.b y 1) (tvec n.b y 2) =
      bn * (gramK n.b).det - bd * qform n.b y := by
  have c10 := dot_comm' (n.b 1) (n.b 0)
  have c20 := dot_comm' (n.b 2) (n.b 0)
  have c21 := dot_comm' (n.b 2) (n.b 1)
  simp [Fv, FC3.ofNode, gk, qform, tvec, Matrix.det_fin_three, Matrix.adjugate_fin_three, dotProduct,
    Matrix.mulVec, Fin.sum_univ_three, gramK, Matrix.vecHead, Matrix.vecTail, c10, c20, c21]
  ring

/-! ## 3. The lift has the coordinates `t` -/

theorem tvec_lift3 (n : NodeW 2 3) (bn bd : ℤ) (t : Fin 3 → ℤ) :
    tvec n.b (toV5 (lift3 (FC3.ofNode n bn bd) (t 0) (t 1) (t 2))) = t := by
  obtain ⟨a, b, h⟩ := lift3_form (FC3.ofNode n bn bd) (t 0) (t 1) (t 2)
  have e : toV5 (lift3 (FC3.ofNode n bn bd) (t 0) (t 1) (t 2)) =
      fun c => (∑ k, t k * n.r k c) + ∑ k : Fin 2, (![-a, -b] : Fin 2 → ℤ) k * hN n.rows k.val c := by
    funext c
    rw [h c]
    fin_cases c <;> simp [Fin.sum_univ_three, Fin.sum_univ_two, FC3.ofNode, hN] <;> ring
  rw [e]
  exact tvec_lift n.id t _

/-! ## 4. gcd and e_i filters -/

theorem gcdF3_of {t : Fin 3 → ℤ} (h : GcdOne t) : gcdF3 (t 0) (t 1) (t 2) = true := by
  obtain ⟨u, hu⟩ := bezout_of_gcd t h
  set g : ℕ := Nat.gcd (Nat.gcd (t 0).natAbs (t 1).natAbs) (t 2).natAbs with hg
  have d2 : g ∣ (t 2).natAbs := Nat.gcd_dvd_right _ _
  have g2 : g ∣ Nat.gcd (t 0).natAbs (t 1).natAbs := Nat.gcd_dvd_left _ _
  have d1 : g ∣ (t 1).natAbs := g2.trans (Nat.gcd_dvd_right _ _)
  have d0 : g ∣ (t 0).natAbs := g2.trans (Nat.gcd_dvd_left _ _)
  have e : ∀ x : ℤ, g ∣ x.natAbs → (g : ℤ) ∣ x := fun x hx => Int.natCast_dvd.2 hx
  have hs : (g : ℤ) ∣ ∑ i, t i * u i := by
    simp only [Fin.sum_univ_three]
    exact dvd_add (dvd_add (Dvd.dvd.mul_right (e _ d0) _) (Dvd.dvd.mul_right (e _ d1) _))
      (Dvd.dvd.mul_right (e _ d2) _)
  rw [hu] at hs
  have h1 : g ∣ 1 := by exact_mod_cast hs
  have h2 : g = 1 := Nat.dvd_one.1 h1
  unfold gcdF3
  rw [← hg, h2]; rfl

theorem eiF3_imp {n : NodeW 2 3} {bn bd : ℤ} {t : Fin 3 → ℤ}
    (h : eiF3 (FC3.ofNode n bn bd) (t 0) (t 1) (t 2) = true) : eiBad n.b t := by
  have key : ∀ i : Fin 5, eiAt3 (n.b 0 i) (n.b 1 i) (n.b 2 i) (t 0) (t 1) (t 2) = true →
      ∀ a a' : Fin 3, a < a' → n.b a i * t a' = n.b a' i * t a := by
    intro i hi a a' hlt
    simp only [eiAt3, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨h01, h02⟩, h12⟩ := hi
    fin_cases a <;> fin_cases a' <;> simp at hlt ⊢ <;> first | exact h01 | exact h02 | exact h12
  simp only [eiF3, FC3.ofNode, Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h)
  · exact ⟨0, key 0 h⟩
  · exact ⟨1, key 1 h⟩
  · exact ⟨2, key 2 h⟩
  · exact ⟨3, key 3 h⟩
  · exact ⟨4, key 4 h⟩

end L5S4
end LRSpectrumFull

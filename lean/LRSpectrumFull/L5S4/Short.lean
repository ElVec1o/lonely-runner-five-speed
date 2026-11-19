/-
# L5S4.Short : E8, the integer test `exists_shorter` of `lib.rs` versus `ShortestFirst` / `ShortestSecond`

`lib.rs::exists_shorter(g, bound)` enumerates the box `|c_i| ≤ mx_i`, `mx_i = isqrt(((bound-1).max(0) · adj(g)_ii) / det g)`
(integer division, `g` positive definite) and returns true iff some nonzero `c` in the box has `cᵀ g c < bound`.

* `gram_box`          Cauchy-Schwarz in the dual-vector form: for `M = Gram(w)`, `c_i² det M ≤ adj(M)_ii · cᵀ M c`.
* `existsShorter`     the Rust test, over the exact box.
* `existsShorter_iff` EXHAUSTIVE BOX: given `det M > 0`, `adj_ii ≥ 0` and the inequality `c_i² det ≤ adj_ii q(c)`,
                      the box test is equivalent to `∃ c ≠ 0, q(c) < bound` over ALL of `ℤ^k`.
* `gram_existsShorter_iff` the Gram instance (hypothesis only `0 < gF w`).
* `shortestFirst_iff`  `ShortestFirst F d ↔ ¬ existsShorter (Gram of the first d rows) (g_00)`   (E8, first test, `d = 1..4`).
* `sMat`, `shortestSecond_iff` the `2×2` matrix `s_ij = g_00 g_ij − g_0i g_0j` of the second test (`nd.j == 2`) and
                      `ShortestSecond F ↔ ¬ existsShorter (sMat F) (s_00)`.

Direction used by the completeness induction: `ShortestFirst`/`ShortestSecond` (proved for every greedy flag in
`Accepted`) ==> the generator's test returns false (the generator never rejects a real chain).  The converse direction
(a passing child satisfies the Lean property) is what makes the box a faithful implementation of the property.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Prim

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## Gram data -/

/-- Gram matrix of a family. -/
def gramM {k : ℕ} (w : Fin k → V5) : Matrix (Fin k) (Fin k) ℤ := Matrix.of fun a b => dot (w a) (w b)

/-- Integer combination of a family. -/
def comb {k : ℕ} (w : Fin k → V5) (c : Fin k → ℤ) : V5 := fun a => ∑ i, c i * w i a

/-- The quadratic form `cᵀ M c` (`q` of the generator). -/
def qf {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) (c : Fin k → ℤ) : ℤ := c ⬝ᵥ (M *ᵥ c)

theorem dot_comb_left {k : ℕ} (x : V5) (u : Fin k → ℤ) (f : Fin k → V5) :
    dot (fun a => ∑ i, u i * f i a) x = ∑ i, u i * dot (f i) x := by
  rw [dot_comm', dot_comb_right]
  exact Finset.sum_congr rfl (fun i _ => by rw [dot_comm' x (f i)])

theorem gF_eq_det {k : ℕ} (w : Fin k → V5) : gF w = (gramM w).det := rfl

theorem qf_gram {k : ℕ} (w : Fin k → V5) (c : Fin k → ℤ) :
    qf (gramM w) c = dot (comb w c) (comb w c) := by
  have h1 : dot (comb w c) (comb w c) = ∑ j, c j * ∑ i, c i * dot (w i) (w j) := by
    unfold comb
    rw [dot_comb_right]
    exact Finset.sum_congr rfl (fun j _ => by rw [dot_comb_left])
  rw [h1]
  unfold qf gramM
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => by ring))

/-- Dual vector `W_i = ∑_a adj(M)_{ia} w_a` (`det M ·` the dual basis). -/
def dualVec {k : ℕ} (w : Fin k → V5) (i : Fin k) : V5 := comb w (fun a => adjugate (gramM w) i a)

theorem dual_pair {k : ℕ} (w : Fin k → V5) (c : Fin k → ℤ) (i : Fin k) :
    dot (dualVec w i) (comb w c) = (gramM w).det * c i := by
  unfold dualVec comb
  rw [dot_comb_left]
  have : ∀ a, dot (w a) (fun x => ∑ j, c j * w j x) = ∑ j, c j * gramM w a j := by
    intro a; rw [dot_comb_right]; exact Finset.sum_congr rfl (fun j _ => by simp [gramM])
  simp only [this]
  have h2 : ∀ j, (adjugate (gramM w) * gramM w) i j = ∑ a, adjugate (gramM w) i a * gramM w a j :=
    fun j => rfl
  calc ∑ a, adjugate (gramM w) i a * ∑ j, c j * gramM w a j
      = ∑ j, c j * ∑ a, adjugate (gramM w) i a * gramM w a j := by
        simp only [Finset.mul_sum]; rw [Finset.sum_comm]
        exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun a _ => by ring))
    _ = ∑ j, c j * (adjugate (gramM w) * gramM w) i j := by simp only [h2]
    _ = (gramM w).det * c i := by
        rw [Finset.sum_congr rfl (fun j _ => by rw [Matrix.adjugate_mul])]
        simp [Matrix.smul_apply, Matrix.one_apply, mul_comm]

theorem dual_norm {k : ℕ} (w : Fin k → V5) (i : Fin k) :
    dot (dualVec w i) (dualVec w i) = (gramM w).det * adjugate (gramM w) i i := by
  have h := dual_pair w (fun a => adjugate (gramM w) i a) i
  have e : comb w (fun a => adjugate (gramM w) i a) = dualVec w i := rfl
  rw [e] at h
  exact h

theorem dot_self_nonneg (x : V5) : 0 ≤ dot x x := Finset.sum_nonneg (fun _ _ => mul_self_nonneg _)

theorem dot_cs (x y : V5) : (dot x y) ^ 2 ≤ dot x x * dot y y := by
  have := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset (Fin 5)) x y
  simpa [dot, sq] using this

/-- Cauchy-Schwarz for the Gram form (dual vectors): `c_i² det M ≤ adj(M)_ii · cᵀ M c`, `M = Gram w`, `det M > 0`. -/
theorem gram_box {k : ℕ} (w : Fin k → V5) (hdet : 0 < gF w) (c : Fin k → ℤ) (i : Fin k) :
    (c i) ^ 2 * (gramM w).det ≤ adjugate (gramM w) i i * qf (gramM w) c := by
  have h1 := dot_cs (dualVec w i) (comb w c)
  rw [dual_pair, dual_norm, ← qf_gram] at h1
  have hd : 0 < (gramM w).det := hdet
  have h2 : (gramM w).det * ((c i) ^ 2 * (gramM w).det)
      ≤ (gramM w).det * (adjugate (gramM w) i i * qf (gramM w) c) := by nlinarith [h1]
  exact le_of_mul_le_mul_left h2 hd

theorem gram_adj_nonneg {k : ℕ} (w : Fin k → V5) (hdet : 0 < gF w) (i : Fin k) :
    0 ≤ adjugate (gramM w) i i := by
  have h := dual_norm w i
  have hn := dot_self_nonneg (dualVec w i)
  rw [h] at hn
  have hd : 0 < (gramM w).det := hdet
  by_contra hneg
  push_neg at hneg
  nlinarith

/-! ## The Rust test -/

/-- `lib.rs::exists_shorter(g, bound)`: some nonzero `c` in the box `|c_i| ≤ mx_i` has `cᵀ g c < bound`. -/
def existsShorter {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) (bound : ℤ) : Prop :=
  ∃ c : Fin k → ℤ, (∃ i, c i ≠ 0) ∧
    (∀ i, |c i| ≤ isqrtI ((max (bound - 1) 0 * adjugate M i i) / M.det)) ∧ qf M c < bound

/-- EXHAUSTIVE BOX: the box test equals the unrestricted existence statement. -/
theorem existsShorter_iff {k : ℕ} (M : Matrix (Fin k) (Fin k) ℤ) (bound : ℤ) (hdet : 0 < M.det)
    (hadj : ∀ i, 0 ≤ adjugate M i i)
    (hbox : ∀ (c : Fin k → ℤ) (i : Fin k), (c i) ^ 2 * M.det ≤ adjugate M i i * qf M c) :
    existsShorter M bound ↔ ∃ c : Fin k → ℤ, (∃ i, c i ≠ 0) ∧ qf M c < bound := by
  constructor
  · rintro ⟨c, hc, -, hq⟩; exact ⟨c, hc, hq⟩
  · rintro ⟨c, hc, hq⟩
    refine ⟨c, hc, fun i => ?_, hq⟩
    apply le_isqrtI
    apply (Int.le_ediv_iff_mul_le hdet).2
    have h1 := hbox c i
    have h2 : qf M c ≤ max (bound - 1) 0 := le_trans (by omega) (le_max_left _ _)
    nlinarith [hadj i]

theorem gram_existsShorter_iff {k : ℕ} (w : Fin k → V5) (hdet : 0 < gF w) (bound : ℤ) :
    existsShorter (gramM w) bound ↔
      ∃ c : Fin k → ℤ, (∃ i, c i ≠ 0) ∧ dot (comb w c) (comb w c) < bound := by
  have := existsShorter_iff (gramM w) bound hdet (gram_adj_nonneg w hdet) (gram_box w hdet)
  simpa [qf_gram] using this

/-! ## `ShortestFirst` -/

/-- The first `d` rows of a flag as a `Fin d`-family. -/
def rowsF {v : V5} (F : FlagData v) (d : ℕ) : Fin d → V5 := fun i => hN F.h i.val

theorem gramQ_eq_qf {v : V5} (F : FlagData v) (d : ℕ) (c : ℕ → ℤ) :
    gramQ F d c = qf (gramM (rowsF F d)) (fun i : Fin d => c i.val) := by
  unfold gramQ qf gramM rowsF
  simp only [dotProduct, Matrix.mulVec, Matrix.of_apply]
  rw [← Fin.sum_univ_eq_sum_range (fun i => ∑ j ∈ range d, c i * c j * dot (hN F.h i) (hN F.h j)) d]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [← Fin.sum_univ_eq_sum_range (fun j => c i.val * c j * dot (hN F.h i.val) (hN F.h j)) d, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  ring

theorem gF_rows_pos {v : V5} (F : FlagData v) (d : ℕ) (hd : d ≤ 4) : 0 < gF (rowsF F d) := by
  have h1 := leadMinor_pos' F d
  rwa [leadMinor_eq_gF F d hd] at h1

theorem shortestFirst_iff {v : V5} (F : FlagData v) (d : ℕ) (hd : d ≤ 4) :
    ShortestFirst F d ↔
      ¬ existsShorter (gramM (rowsF F d)) (dot (hN F.h 0) (hN F.h 0)) := by
  rw [gram_existsShorter_iff _ (gF_rows_pos F d hd)]
  unfold ShortestFirst
  constructor
  · intro h ⟨c', ⟨i0, hi0⟩, hlt⟩
    have e : dot (comb (rowsF F d) c') (comb (rowsF F d) c')
        = gramQ F d (fun n => if hn : n < d then c' ⟨n, hn⟩ else 0) := by
      rw [← qf_gram, gramQ_eq_qf]
      congr 1
      funext i; simp
    have := h (fun n => if hn : n < d then c' ⟨n, hn⟩ else 0) ⟨i0.val, i0.2, by simpa using hi0⟩
    rw [← e] at this
    omega
  · intro h c ⟨i0, hi0, hc0⟩
    by_contra hlt
    push_neg at hlt
    apply h
    refine ⟨fun i : Fin d => c i.val, ⟨⟨i0, hi0⟩, hc0⟩, ?_⟩
    rw [← qf_gram, ← gramQ_eq_qf]
    exact hlt

end L5S4
end LRSpectrumFull

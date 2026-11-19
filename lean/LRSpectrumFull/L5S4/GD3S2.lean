/-
# L5S4.GD3S2 : soundness of the flat depth-3 child checker, part 2 (stage S4 block 10)

The greedy tests and the bridge `ChildPass n y -> passPoint3 (FC3.ofNode n bn bd) (b y) = true` for EVERY node `n : NodeW 2 3`.

* `short3_exists`        the 3-D box search returns `true` only for a nonzero short combination;
* `det_sMatR`, `sMatR_existsShorter_iff`  node-row version of `Short2.shortestSecond_iff` (`s` matrix, rows of a node);
* `greedy3_false`        a passing child is not rejected by `greedy3F` (representative invariance for two chain rows:
                         the lift `lift3` and `y` differ by `κ0 l0 + κ1 l1`, `existsShorter` transports by a shear);
* `passPoint3_of_childPass`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3S1

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. Unpacking the boolean searches -/

theorem short3_exists {g00 g01 g02 g11 g12 g22 : ℤ} (h : short3 g00 g01 g02 g11 g12 g22 = true) :
    ∃ c0 c1 c2 : ℤ, ((c0 ≠ 0 ∨ c1 ≠ 0) ∨ c2 ≠ 0) ∧
      g00 * c0 * c0 + g11 * c1 * c1 + g22 * c2 * c2 + 2 * (g01 * c0 * c1 + g02 * c0 * c2 + g12 * c1 * c2) < g00 := by
  unfold short3 at h
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨c0, -, c1, -, c2, -, h1, h2⟩ := h
  exact ⟨c0, c1, c2, h1, h2⟩

/-! ## 2. The `s` matrix of a node -/

theorem det_sMatR (rw : Fin 4 → V5) :
    (sMatR rw).det = dot (hN rw 0) (hN rw 0) * gF (rowsR rw 3) := by
  rw [gF_eq_det]
  have c10 := dot_comm' (hN rw 1) (hN rw 0)
  have c20 := dot_comm' (hN rw 2) (hN rw 0)
  have c21 := dot_comm' (hN rw 2) (hN rw 1)
  simp [Matrix.det_fin_two, Matrix.det_fin_three, sMatR, gramM, rowsR, sgmR, c10, c20, c21]
  ring

theorem sgmR_diag_nonneg (rw : Fin 4 → V5) (i : ℕ) : 0 ≤ sgmR rw i i := by
  unfold sgmR
  have := dot_cs (hN rw 0) (hN rw i)
  nlinarith [dot_self_nonneg (hN rw 0)]

theorem qf_sMatR (rw : Fin 4 → V5) (c : Fin 2 → ℤ) :
    qf (sMatR rw) c = c 0 * c 0 * sgmR rw 1 1 + 2 * c 0 * c 1 * sgmR rw 1 2 + c 1 * c 1 * sgmR rw 2 2 := by
  simp [qf, sMatR, dotProduct, Matrix.mulVec, Fin.sum_univ_two]
  ring

theorem sMatR_existsShorter_iff (rw : Fin 4 → V5) (hg : 0 < dot (hN rw 0) (hN rw 0)) (hG : 0 < gF (rowsR rw 3))
    (bound : ℤ) :
    existsShorter (sMatR rw) bound ↔ ∃ c : Fin 2 → ℤ, (∃ i, c i ≠ 0) ∧ qf (sMatR rw) c < bound := by
  have hdet : 0 < (sMatR rw).det := by rw [det_sMatR]; exact mul_pos hg hG
  have hadj : ∀ i, 0 ≤ adjugate (sMatR rw) i i := by
    intro i
    fin_cases i
    · simp [Matrix.adjugate_fin_two, sMatR]; exact sgmR_diag_nonneg rw 2
    · simp [Matrix.adjugate_fin_two, sMatR]; exact sgmR_diag_nonneg rw 1
  have hbox : ∀ (c : Fin 2 → ℤ) (i : Fin 2),
      (c i) ^ 2 * (sMatR rw).det ≤ adjugate (sMatR rw) i i * qf (sMatR rw) c := by
    intro c i
    rw [qf_sMatR]
    fin_cases i
    · simp [Matrix.adjugate_fin_two, Matrix.det_fin_two, sMatR]
      nlinarith [sq_nonneg (sgmR rw 1 2 * c 0 + sgmR rw 2 2 * c 1)]
    · simp [Matrix.adjugate_fin_two, Matrix.det_fin_two, sMatR]
      nlinarith [sq_nonneg (sgmR rw 1 1 * c 0 + sgmR rw 1 2 * c 1)]
  exact existsShorter_iff _ _ hdet hadj hbox

/-! ## 3. Positivity -/

theorem dot_pos_of_rinv (x s : V5) (h : dot x s = 1) : 0 < dot x x := by
  rcases (dot_self_nonneg x).lt_or_eq with h1 | h1
  · exact h1
  · exfalso
    have h0 : ∀ k ∈ Finset.univ, x k * x k = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => mul_self_nonneg _)).1 h1.symm
    have hz : ∀ k, x k = 0 := fun k => mul_self_eq_zero.1 (h0 k (Finset.mem_univ k))
    have : dot x s = 0 := by simp [dot, hz]
    rw [h] at this; exact one_ne_zero this

theorem qform_pos_gen {j d : ℕ} (hjd : j + d = 5) {l : Fin j → V5} {b : Fin d → V5} {s : Fin j → V5} {r : Fin d → V5}
    (hN : NodeId l b s r) (y : V5) (hg : GcdOne (tvec b y)) : 0 < qform b y := by
  obtain ⟨s', hs'⟩ := ext_ls hN y hg
  rw [← gF_snoc hjd hN y]
  exact gF_pos_of_rinv _ s' hs'

theorem snoc_rows2 (n : NodeW 2 3) (y : V5) :
    rowsR (setRow n.rows 2 y) (2 + 1) = Fin.snoc (α := fun _ => V5) (fun i : Fin 2 => hN n.rows i.val) y := by
  funext i
  fin_cases i
  · simp [rowsR, setRow, hN, Fin.snoc]
  · simp [rowsR, setRow, hN, Fin.snoc]
  · simp [rowsR, setRow, hN, Fin.snoc]

theorem rows_y_apply (n : NodeW 2 3) (y : V5) :
    hN (setRow n.rows 2 y) 0 = n.rows 0 ∧ hN (setRow n.rows 2 y) 1 = n.rows 1 ∧ hN (setRow n.rows 2 y) 2 = y := by
  refine ⟨?_, ?_, ?_⟩ <;> simp [hN, setRow]

/-! ## 4. Dot identities for the shifted row -/

theorem dot_shift_l0 (l0 l1 y yl : V5) (κ0 κ1 : ℤ) (hy : ∀ a, yl a = y a + κ0 * l0 a + κ1 * l1 a) :
    dot l0 yl = dot l0 y + κ0 * dot l0 l0 + κ1 * dot l0 l1 := by
  unfold dot; simp only [hy, Fin.sum_univ_five]; ring

theorem dot_shift_l1 (l0 l1 y yl : V5) (κ0 κ1 : ℤ) (hy : ∀ a, yl a = y a + κ0 * l0 a + κ1 * l1 a) :
    dot l1 yl = dot l1 y + κ0 * dot l0 l1 + κ1 * dot l1 l1 := by
  unfold dot; simp only [hy, Fin.sum_univ_five]; ring

theorem dot_shift_yy (l0 l1 y yl : V5) (κ0 κ1 : ℤ) (hy : ∀ a, yl a = y a + κ0 * l0 a + κ1 * l1 a) :
    dot yl yl = dot y y + 2 * κ0 * dot l0 y + 2 * κ1 * dot l1 y + κ0 * κ0 * dot l0 l0 + 2 * κ0 * κ1 * dot l0 l1 +
      κ1 * κ1 * dot l1 l1 := by
  unfold dot; simp only [hy, Fin.sum_univ_five]; ring

theorem dot_comb3 (l0 l1 yl : V5) (c0 c1 c2 : ℤ) :
    dot (fun a => c0 * l0 a + c1 * l1 a + c2 * yl a) (fun a => c0 * l0 a + c1 * l1 a + c2 * yl a) =
      dot l0 l0 * c0 * c0 + dot l1 l1 * c1 * c1 + dot yl yl * c2 * c2 +
      2 * (dot l0 l1 * c0 * c1 + dot l0 yl * c0 * c2 + dot l1 yl * c1 * c2) := by
  unfold dot; simp only [Fin.sum_univ_five]; ring

theorem comb3_shift (n : NodeW 2 3) (y yl : V5) (c0 c1 c2 κ0 κ1 : ℤ)
    (hy : ∀ a, yl a = y a + κ0 * n.rows 0 a + κ1 * n.rows 1 a) :
    comb (rowsR (setRow n.rows 2 y) (2 + 1)) ![c0 + c2 * κ0, c1 + c2 * κ1, c2] =
      fun a => c0 * n.rows 0 a + c1 * n.rows 1 a + c2 * yl a := by
  obtain ⟨h0, h1, h2⟩ := rows_y_apply n y
  funext a
  show comb (rowsR (setRow n.rows 2 y) 3) ![c0 + c2 * κ0, c1 + c2 * κ1, c2] a = _
  have e0 : rowsR (setRow n.rows 2 y) 3 0 = n.rows 0 := h0
  have e1 : rowsR (setRow n.rows 2 y) 3 1 = n.rows 1 := h1
  have e2 : rowsR (setRow n.rows 2 y) 3 2 = y := h2
  simp only [comb, Fin.sum_univ_three, e0, e1, e2, hy a]
  simp
  ring

/-! ## 5. Definitions of the six Gram numbers of `greedy3G` -/

def G00 (f : FC3) : ℤ := f.p0 * f.p0 + f.p1 * f.p1 + f.p2 * f.p2 + f.p3 * f.p3 + f.p4 * f.p4
def G01 (f : FC3) : ℤ := f.p0 * f.q0 + f.p1 * f.q1 + f.p2 * f.q2 + f.p3 * f.q3 + f.p4 * f.q4
def G11 (f : FC3) : ℤ := f.q0 * f.q0 + f.q1 * f.q1 + f.q2 * f.q2 + f.q3 * f.q3 + f.q4 * f.q4
def G02 (f : FC3) (y : Y5) : ℤ := f.p0 * y.1 + f.p1 * y.2.1 + f.p2 * y.2.2.1 + f.p3 * y.2.2.2.1 + f.p4 * y.2.2.2.2
def G12 (f : FC3) (y : Y5) : ℤ := f.q0 * y.1 + f.q1 * y.2.1 + f.q2 * y.2.2.1 + f.q3 * y.2.2.2.1 + f.q4 * y.2.2.2.2
def G22 (y : Y5) : ℤ := y.1 * y.1 + y.2.1 * y.2.1 + y.2.2.1 * y.2.2.1 + y.2.2.2.1 * y.2.2.2.1 + y.2.2.2.2 * y.2.2.2.2

theorem greedy3F_eq (f : FC3) (t0 t1 t2 : ℤ) :
    greedy3F f t0 t1 t2 =
      (short3 (G00 f) (G01 f) (G02 f (lift3 f t0 t1 t2)) (G11 f) (G12 f (lift3 f t0 t1 t2)) (G22 (lift3 f t0 t1 t2)) ||
        shortB (G00 f * G11 f - G01 f * G01 f)
          (G00 f * G12 f (lift3 f t0 t1 t2) - G01 f * G02 f (lift3 f t0 t1 t2))
          (G00 f * G22 (lift3 f t0 t1 t2) - G02 f (lift3 f t0 t1 t2) * G02 f (lift3 f t0 t1 t2))) := rfl

section Greedy
variable (n : NodeW 2 3) (bn bd : ℤ)

theorem G_eq (Y : Y5) :
    G00 (FC3.ofNode n bn bd) = dot (n.rows 0) (n.rows 0) ∧ G01 (FC3.ofNode n bn bd) = dot (n.rows 0) (n.rows 1) ∧
    G11 (FC3.ofNode n bn bd) = dot (n.rows 1) (n.rows 1) ∧
    G02 (FC3.ofNode n bn bd) Y = dot (n.rows 0) (toV5 Y) ∧ G12 (FC3.ofNode n bn bd) Y = dot (n.rows 1) (toV5 Y) ∧
    G22 Y = dot (toV5 Y) (toV5 Y) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [G00, G01, G11, G02, G12, G22, dot, Fin.sum_univ_five, FC3.ofNode, toV5]

end Greedy

/-! ## 6. A passing child is not rejected by the flat greedy test -/

theorem greedy3_false (n : NodeW 2 3) (bn bd : ℤ) (y : V5) (hp : ChildPass n y) :
    greedy3F (FC3.ofNode n bn bd) (tvec n.b y 0) (tvec n.b y 1) (tvec n.b y 2) = false := by
  by_contra hne
  have hT : greedy3F (FC3.ofNode n bn bd) (tvec n.b y 0) (tvec n.b y 1) (tvec n.b y 2) = true := by simpa using hne
  rw [greedy3F_eq] at hT
  set Y := lift3 (FC3.ofNode n bn bd) (tvec n.b y 0) (tvec n.b y 1) (tvec n.b y 2) with hY
  set yl : V5 := toV5 Y with hyl
  have htv : tvec n.b yl = tvec n.b y := tvec_lift3 n bn bd (tvec n.b y)
  have hs := lat_of_same_coords (by norm_num : 2 + 3 = 5) n.id y yl (fun i => by
    have := congrFun htv i; exact this.symm)
  obtain ⟨κ0, κ1, hy⟩ : ∃ κ0 κ1 : ℤ, ∀ a, yl a = y a + κ0 * n.rows 0 a + κ1 * n.rows 1 a := by
    refine ⟨dot (n.s 0) (fun c => yl c - y c), dot (n.s 1) (fun c => yl c - y c), fun a => ?_⟩
    have := hs a
    simp only [Fin.sum_univ_two, Fin.val_zero, Fin.val_one, hN_zero, hN_one] at this
    rw [this]; ring
  have hGe := G_eq n bn bd Y
  have hG00 := hGe.1
  have hG01 := hGe.2.1
  have hG11 := hGe.2.2.1
  have hG02 : G02 (FC3.ofNode n bn bd) Y = dot (n.rows 0) yl := hGe.2.2.2.1
  have hG12 : G12 (FC3.ofNode n bn bd) Y = dot (n.rows 1) yl := hGe.2.2.2.2.1
  have hG22 : G22 Y = dot yl yl := hGe.2.2.2.2.2
  have hgcd := hp.1
  have hdet : 0 < gF (rowsR (setRow n.rows 2 y) (2 + 1)) := by
    rw [snoc_rows2, gF_snoc (by norm_num) n.id y]
    exact qform_pos_gen (by norm_num) n.id y hgcd
  have hg00 : 0 < dot (n.rows 0) (n.rows 0) := by
    have := n.id.ls 0 0
    simp only [if_true] at this
    have h0 : dot (hN n.rows 0) (n.s 0) = 1 := by simpa [hN_zero] using this
    rw [hN_zero] at h0
    exact dot_pos_of_rinv _ _ h0
  rw [Bool.or_eq_true] at hT
  rcases hT with h3 | hs3
  · obtain ⟨c0, c1, c2, hc, hlt⟩ := short3_exists h3
    apply hp.2.2.2.1
    rw [gram_existsShorter_iff _ hdet]
    refine ⟨![c0 + c2 * κ0, c1 + c2 * κ1, c2], ?_, ?_⟩
    · by_cases h2 : c2 = 0
      · rcases hc with (h | h) | h
        · exact ⟨0, by simp [h2, h]⟩
        · exact ⟨1, by simp [h2, h]⟩
        · exact absurd h2 h
      · exact ⟨2, by simpa using h2⟩
    · rw [comb3_shift n y yl c0 c1 c2 κ0 κ1 hy, dot_comb3, hN_zero]
      rw [hG00, hG01, hG11, hG02, hG12, hG22] at hlt
      linarith
  · obtain ⟨c0, c1, hc, hlt⟩ := shortB_exists hs3
    apply hp.2.2.2.2.1 rfl
    obtain ⟨h0, h1, h2⟩ := rows_y_apply n y
    rw [sMatR_existsShorter_iff _ (by rw [h0]; exact hg00) hdet]
    refine ⟨![c0 + c1 * κ1, c1], ?_, ?_⟩
    · by_cases h1' : c1 = 0
      · have h0' : c0 ≠ 0 := by
          rcases hc with h | h
          · exact h
          · exact absurd h1' h
        exact ⟨0, by simp [h1', h0']⟩
      · exact ⟨1, by simpa using h1'⟩
    · rw [qf_sMatR]
      have e11 : sgmR (setRow n.rows 2 y) 1 1 =
          dot (n.rows 0) (n.rows 0) * dot (n.rows 1) (n.rows 1) - dot (n.rows 0) (n.rows 1) * dot (n.rows 0) (n.rows 1) := by
        simp only [sgmR, h0, h1]
      have e12 : sgmR (setRow n.rows 2 y) 1 2 =
          dot (n.rows 0) (n.rows 0) * dot (n.rows 1) y - dot (n.rows 0) (n.rows 1) * dot (n.rows 0) y := by
        simp only [sgmR, h0, h1, h2]
      have e22 : sgmR (setRow n.rows 2 y) 2 2 =
          dot (n.rows 0) (n.rows 0) * dot y y - dot (n.rows 0) y * dot (n.rows 0) y := by
        simp only [sgmR, h0, h2]
      rw [hG00, hG01, hG11, hG02, hG12, hG22] at hlt
      rw [dot_shift_l0 (n.rows 0) (n.rows 1) y yl κ0 κ1 hy, dot_shift_l1 (n.rows 0) (n.rows 1) y yl κ0 κ1 hy,
        dot_shift_yy (n.rows 0) (n.rows 1) y yl κ0 κ1 hy] at hlt
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
      rw [e11, e12, e22]
      linarith [hlt]

/-! ## 7. The bridge -/

theorem passPoint3_of_childPass (n : NodeW 2 3) (bn bd : ℤ) (y : V5) (hp : ChildPass n y) :
    passPoint3 (FC3.ofNode n bn bd) (tvec n.b y 0) (tvec n.b y 1) (tvec n.b y 2) = true := by
  have e1 := gcdF3_of hp.1
  have e2 : eiF3 (FC3.ofNode n bn bd) (tvec n.b y 0) (tvec n.b y 1) (tvec n.b y 2) = false := by
    by_contra h
    exact hp.2.2.1 (eiF3_imp (by simpa using h))
  have e3 := greedy3_false n bn bd y hp
  unfold passPoint3
  rw [e1, e2, e3]
  rfl

end L5S4
end LRSpectrumFull

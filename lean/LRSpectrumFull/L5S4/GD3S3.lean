/-
# L5S4.GD3S3 : soundness of the flat depth-3 child checker, part 3: rows, lists, completeness (stage S4 block 10)

* `rowOk_cover`     the interval record of a row `(t0, t1)` contains every `t2` with `Fv > 0` (concavity of `Fv` in `t2`,
                    leading coefficient `-bd * a22 < 0`; an empty row stores its integer maximiser);
* `rowsOk_mem`      a row list accepted by `rowsOk` stores every passing point of its rows (`rowsPairs`);
* `child_list_complete3`  `ChildPass n y` and `nodeOk` give the stored coordinates `(t1, t2)` of `y` in the group `t0`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3S2

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. Concavity of `Fv` in `t2` and the interval records -/

theorem Fv_conc (f : FC3) (ha : 0 < f.a22) (hbd : 0 < f.bd) (t0 t1 x y z : ℤ) (hxy : x < y) (hyz : y < z) :
    Fv f t0 t1 x * (z - y) + Fv f t0 t1 z * (y - x) ≤ Fv f t0 t1 y * (z - x) := by
  have h1 : 0 < y - x := by linarith
  have h2 : 0 < z - y := by linarith
  have h3 : 0 < z - x := by linarith
  have hprod : 0 < (y - x) * (z - y) * (z - x) := mul_pos (mul_pos h1 h2) h3
  have hk := mul_pos (mul_pos hbd ha) hprod
  have key : Fv f t0 t1 y * (z - x) - (Fv f t0 t1 x * (z - y) + Fv f t0 t1 z * (y - x)) =
      f.bd * f.a22 * ((y - x) * (z - y) * (z - x)) := by
    unfold Fv; ring
  linarith [hk, key]

theorem rowOk_cover (f : FC3) (ha : 0 < f.a22) (hbd : 0 < f.bd) (t0 t1 lo hi t2 : ℤ)
    (h : rowOk f t0 t1 lo hi = true) (hF : 0 < Fv f t0 t1 t2) (hfp : t0 = 0 → t1 = 0 → 0 < t2) :
    lo ≤ t2 ∧ t2 ≤ hi := by
  by_cases hle : lo ≤ hi
  · have hup : (∃ hA : 0 < Fv f t0 t1 lo, ∃ hB : 0 < Fv f t0 t1 hi, ∃ hC : Fv f t0 t1 (hi + 1) ≤ 0, True) := by
      unfold rowOk at h
      rw [if_pos hle] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨hA, hB⟩, hC⟩, -⟩ := h
      exact ⟨hA, hB, hC, trivial⟩
    obtain ⟨hA, hB, hC, -⟩ := hup
    have hupper : t2 ≤ hi := by
      by_contra hcon
      push_neg at hcon
      rcases (show hi + 1 = t2 ∨ hi + 1 < t2 by omega) with he | hlt
      · rw [← he] at hF; linarith
      · have := Fv_conc f ha hbd t0 t1 hi (hi + 1) t2 (by omega) hlt
        nlinarith [mul_pos hB (show (0 : ℤ) < t2 - (hi + 1) by omega),
          mul_nonneg (neg_nonneg.2 hC) (show (0 : ℤ) ≤ t2 - hi by omega)]
    refine ⟨?_, hupper⟩
    by_cases h01 : t0 = 0 ∧ t1 = 0
    · have hl1 : lo = 1 := by
        unfold rowOk at h
        rw [if_pos hle] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨-, hD⟩⟩ := (⟨h⟩ : Nonempty _)
        rw [if_pos h01] at hD
        simpa using hD
      have := hfp h01.1 h01.2
      omega
    · have hD : Fv f t0 t1 (lo - 1) ≤ 0 := by
        unfold rowOk at h
        rw [if_pos hle] at h
        simp only [Bool.and_eq_true, decide_eq_true_eq] at h
        obtain ⟨⟨-, hD⟩⟩ := (⟨h⟩ : Nonempty _)
        rw [if_neg h01] at hD
        simpa using hD
      by_contra hcon
      push_neg at hcon
      rcases (show t2 = lo - 1 ∨ t2 < lo - 1 by omega) with he | hlt
      · rw [he] at hF; linarith
      · have := Fv_conc f ha hbd t0 t1 t2 (lo - 1) lo hlt (by omega)
        nlinarith [mul_pos hA (show (0 : ℤ) < lo - 1 - t2 by omega),
          mul_nonneg (neg_nonneg.2 hD) (show (0 : ℤ) ≤ lo - t2 by omega)]
  · exfalso
    have hE : hi + 1 = lo ∧ Fv f t0 t1 lo ≤ 0 ∧ Fv f t0 t1 (lo - 1) ≤ Fv f t0 t1 lo ∧
        Fv f t0 t1 (lo + 1) ≤ Fv f t0 t1 lo := by
      unfold rowOk at h
      rw [if_neg hle] at h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
      exact ⟨h1, h2, h3, h4⟩
    obtain ⟨-, hm, hdn, hup⟩ := hE
    rcases lt_trichotomy t2 lo with hlt | heq | hgt
    · rcases (show t2 = lo - 1 ∨ t2 < lo - 1 by omega) with he | hlt2
      · rw [he] at hF; linarith
      · have := Fv_conc f ha hbd t0 t1 t2 (lo - 1) lo hlt2 (by omega)
        nlinarith [mul_nonneg (sub_nonneg.2 hdn) (show (0 : ℤ) ≤ lo - t2 by omega)]
    · rw [heq] at hF; linarith
    · rcases (show t2 = lo + 1 ∨ lo + 1 < t2 by omega) with he | hlt2
      · rw [he] at hF; linarith
      · have := Fv_conc f ha hbd t0 t1 lo (lo + 1) t2 (by omega) hlt2
        nlinarith [mul_nonneg (sub_nonneg.2 hup) (show (0 : ℤ) ≤ t2 - lo by omega)]

/-! ## 2. Row lists -/

/-- The `(t1, t2)` pairs stored in a row list (`rowsOk` data format `[t1, lo, hi, np, passes..]`). -/
def rowsPairs : ℕ → ℤ → List ℤ → List (ℤ × ℤ)
  | 0, _, _ => []
  | n + 1, t1, _ :: _ :: _ :: np :: rest =>
      (rest.take np.toNat).map (fun t2 => (t1, t2)) ++ rowsPairs n (t1 + 1) (rest.drop np.toNat)
  | _ + 1, _, _ => []

theorem mem_ptsList {lo hi t : ℤ} (h1 : lo ≤ t) (h2 : t ≤ hi) : t ∈ ptsList lo hi := by
  unfold ptsList
  rw [List.mem_map]
  refine ⟨(t - lo).toNat, ?_, ?_⟩
  · rw [List.mem_range]; omega
  · omega

theorem rowsOk_mem (f : FC3) (ha : 0 < f.a22) (hbd : 0 < f.bd) (t0 : ℤ) :
    ∀ (n : ℕ) (t1s : ℤ) (data : List ℤ), rowsOk f t0 n t1s data = true →
      ∀ t1 t2 : ℤ, t1s ≤ t1 → t1 < t1s + n → 0 < Fv f t0 t1 t2 → (t0 = 0 → t1 = 0 → 0 < t2) →
        passPoint3 f t0 t1 t2 = true → (t1, t2) ∈ rowsPairs n t1s data := by
  intro n
  induction n with
  | zero => intro t1s data _ t1 t2 h1 h2; omega
  | succ n ih =>
    intro t1s data hok t1 t2 h1 h2 hF hfp hpp
    rcases data with _ | ⟨a, _ | ⟨lo, _ | ⟨hi, _ | ⟨np, rest⟩⟩⟩⟩
    · simp [rowsOk] at hok
    · simp [rowsOk] at hok
    · simp [rowsOk] at hok
    · simp [rowsOk] at hok
    · simp only [rowsOk, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨hat, hrow⟩, hpass⟩, hrest⟩ := hok
      simp only [rowsPairs]
      by_cases h : t1 = t1s
      · subst h
        have hc := rowOk_cover f ha hbd t0 t1 lo hi t2 hrow hF hfp
        have hmem : t2 ∈ passRow f t0 t1 lo hi := by
          unfold passRow
          rw [List.mem_filter]
          exact ⟨mem_ptsList hc.1 hc.2, hpp⟩
        rw [← hpass] at hmem
        exact List.mem_append_left _ (List.mem_map.2 ⟨t2, hmem, rfl⟩)
      · have := ih (t1s + 1) (rest.drop np.toNat) hrest t1 t2 (by omega) (by push_cast at h2 ⊢; omega) hF hfp hpp
        exact List.mem_append_right _ this

/-! ## 3. Completeness of the stored list -/

theorem firstPos3 {t : Fin 3 → ℤ} (h : FirstPos t) :
    0 ≤ t 0 ∧ (t 0 = 0 → 0 ≤ t 1) ∧ (t 0 = 0 → t 1 = 0 → 0 < t 2) := by
  obtain ⟨m, hm, hz⟩ := h
  fin_cases m
  · simp only [Fin.zero_eta, Fin.isValue] at hm
    exact ⟨hm.le, fun h => by omega, fun h => by omega⟩
  · have h0 : t 0 = 0 := hz 0 (by decide)
    simp only [Fin.mk_one, Fin.isValue] at hm
    exact ⟨by omega, fun _ => hm.le, fun _ h1 => by omega⟩
  · have h0 : t 0 = 0 := hz 0 (by decide)
    have h1 : t 1 = 0 := hz 1 (by decide)
    simp only [Fin.reduceFinMk, Fin.isValue] at hm
    exact ⟨by omega, fun _ => by omega, fun _ _ => hm⟩

theorem ball_of_pass3 (n : NodeW 2 3) (bn bd : ℤ) (hbd : 0 < bd)
    (hrad : radFrac (Cq (2 + 1)) n.wit n.rows 2 n.rk = (bn : ℚ) / bd) (y : V5) (hp : ChildPass n y) :
    qform n.b y * bd < bn * (gramK n.b).det := by
  have h := hp.2.2.2.2.2
  set R := radFrac (Cq (2 + 1)) n.wit n.rows 2 n.rk with hR
  set G := (gramK n.b).det with hG
  have hden : (0 : ℤ) < (R.den : ℤ) := by exact_mod_cast R.den_pos
  have hbdq : (bd : ℚ) ≠ 0 := by exact_mod_cast hbd.ne'
  have hdq : (R.den : ℚ) ≠ 0 := by exact_mod_cast R.den_nz
  have e : R.num * bd = bn * (R.den : ℤ) := by
    have h1 : (R.num : ℚ) / (R.den : ℚ) = (bn : ℚ) / bd := by rw [Rat.num_div_den, hrad]
    rw [div_eq_div_iff hdq hbdq] at h1
    exact_mod_cast h1
  have h1 : (qform n.b y * (R.den : ℤ)) * bd < (R.num * G) * bd := mul_lt_mul_of_pos_right h hbd
  have h3 : (R.num * G) * bd = (bn * G) * (R.den : ℤ) := by linear_combination G * e
  have h4 : (qform n.b y * (R.den : ℤ)) * bd = (qform n.b y * bd) * (R.den : ℤ) := by ring
  rw [h3, h4] at h1
  exact lt_of_mul_lt_mul_right h1 hden.le

/-- **List completeness at depth 3.**  If the stored data passes `nodeOk` (keys `0..T0`, every row interval and every stored
pass list checked), every `y` with `ChildPass n y` has its coordinates `(t1, t2)` stored in the group `t0`. -/
theorem child_list_complete3 (n : NodeW 2 3) (bn bd : ℤ) (hbd : 0 < bd)
    (hrad : radFrac (Cq (2 + 1)) n.wit n.rows 2 n.rk = (bn : ℚ) / bd)
    (ha : 0 < (FC3.ofNode n bn bd).a22)
    (G : List (ℤ × List ℤ)) (hok : nodeOk (FC3.ofNode n bn bd) G = true) (y : V5) (hp : ChildPass n y) :
    ∃ g ∈ G, g.1 = tvec n.b y 0 ∧
      (tvec n.b y 1, tvec n.b y 2) ∈
        rowsPairs (nRows (FC3.ofNode n bn bd) g.1) (firstT1 (FC3.ofNode n bn bd) g.1) g.2 := by
  have hpp := passPoint3_of_childPass n bn bd y hp
  have hq := ball_of_pass3 n bn bd hbd hrad y hp
  have hFv : 0 < Fv (FC3.ofNode n bn bd) (tvec n.b y 0) (tvec n.b y 1) (tvec n.b y 2) := by
    rw [Fv_eq]; linarith
  have hbox : ∀ i : Fin 3, |tvec n.b y i| ≤ isqrtI (bn * gramK n.b i i / bd) :=
    fun i => box_covers (by norm_num) n.id y i bn bd hbd hq
  have hb0 := abs_le.1 (hbox 0)
  have hb1 := abs_le.1 (hbox 1)
  obtain ⟨hf0, hf1, hf2⟩ := firstPos3 hp.2.1
  have hT0 : (FC3.ofNode n bn bd).T0 = isqrtI (bn * gramK n.b 0 0 / bd) := rfl
  have hT1 : (FC3.ofNode n bn bd).T1 = isqrtI (bn * gramK n.b 1 1 / bd) := rfl
  unfold nodeOk at hok
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hok
  obtain ⟨hkeys, hall⟩ := hok
  have h0mem : tvec n.b y 0 ∈ G.map Prod.fst := by
    rw [hkeys, List.mem_map]
    refine ⟨(tvec n.b y 0).toNat, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · omega
  obtain ⟨g, hg, hg0⟩ := List.mem_map.1 h0mem
  refine ⟨g, hg, hg0, ?_⟩
  have hrow := hall g hg
  have hlo : firstT1 (FC3.ofNode n bn bd) g.1 ≤ tvec n.b y 1 ∧
      tvec n.b y 1 < firstT1 (FC3.ofNode n bn bd) g.1 + (nRows (FC3.ofNode n bn bd) g.1 : ℤ) := by
    unfold firstT1 nRows
    by_cases hz : g.1 = 0
    · rw [if_pos hz, if_pos hz]
      have := hf1 (by rw [← hg0]; exact hz)
      omega
    · rw [if_neg hz, if_neg hz]
      omega
  exact rowsOk_mem (FC3.ofNode n bn bd) ha hbd g.1 _ _ g.2 hrow (tvec n.b y 1) (tvec n.b y 2) hlo.1 hlo.2
    (by rw [hg0]; exact hFv) (fun h0 h1 => hf2 (by rw [← hg0]; exact h0) h1) (by rw [hg0]; exact hpp)

end L5S4
end LRSpectrumFull

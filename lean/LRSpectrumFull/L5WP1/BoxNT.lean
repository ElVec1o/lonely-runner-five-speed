/-
# WP1 box theorem: exact values of the near-tight tuples

* `val_fam1`, `val_fam2`: `ML (1,2,3,4,5s) = s/(5s+1)` and `ML (1,3,4,7,5s) = s/(5s+1)` (`s >= 2`), from `ObsKS5Tail`.
* `okC`, `lowOK`: lower bound `ML >= pn/pd` from one rational time `x/q` (integer cross-multiplication).
* `chainOK`: upper bound `ML <= pn/pd` from a finite cover of `[0, 1]` by closed intervals
  `[(m pd - pn)/(pd w), (m pd + pn)/(pd w)]`, `w` a speed (a time in such an interval has `||w t|| <= pn/pd`);
  the chain is checked left to right in integer arithmetic scaled by `pd * lcm`.
* `ml_eq_of_data`: both together give `ML (vecL [a,b,c,d,e]) = pn/pd`; used for the sporadic tuples, whose data
  (time, lcm, chain) come from an untrusted generator and are re-checked by `decide +kernel`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.ObsKS5Tail

namespace L5W

open LRSpectrumFull

/-- the speed vector of a list of five naturals -/
def vecL (l : List ℕ) : Fin 5 → ℤ := fun i => ((l.getD i 0 : ℕ) : ℤ)

/-! ### the two infinite families -/

theorem val_fam1 (s e : ℕ) (hs : 1 ≤ s) (he : e = 5 * s) :
    ML (vecL [1, 2, 3, 4, e]) = (s : ℝ) / (5 * s + 1) := by
  have h : vecL [1, 2, 3, 4, e] = (![1, 2, 3, 4, 5 * (s : ℤ)] : Fin 5 → ℤ) := by
    funext i; subst he; fin_cases i <;> simp [vecL]
  rw [h]; exact KS5Tail.ML_V1_eq s hs

theorem val_fam2 (s e : ℕ) (hs : 2 ≤ s) (he : e = 5 * s) :
    ML (vecL [1, 3, 4, 7, e]) = (s : ℝ) / (5 * s + 1) := by
  have h : vecL [1, 3, 4, 7, e] = (![1, 3, 4, 7, 5 * (s : ℤ)] : Fin 5 → ℤ) := by
    funext i; subst he; fin_cases i <;> simp [vecL]
  rw [h]; exact KS5Tail.ML_V2_eq s hs

/-! ### lower bound from one time -/

def okC (pn pd x q v : ℕ) : Bool := Nat.ble (pn * q) (pd * Nat.min (v * x % q) (q - v * x % q))

def lowOK (pn pd x q : ℕ) (ws : List ℕ) : Bool := Nat.blt 0 q && ws.all (okC pn pd x q)

theorem okC_real {pn pd x q v : ℕ} (hq : 0 < q) (hpd : 0 < pd) (h : okC pn pd x q v = true) :
    (pn : ℝ) / pd ≤ nearestIntDist ((v : ℝ) * ((x : ℝ) / q)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hpd' : (0 : ℝ) < pd := by exact_mod_cast hpd
  have e : (v : ℝ) * ((x : ℝ) / q) = ((v * x : ℕ) : ℝ) / ((q : ℕ) : ℝ) := by push_cast; ring
  rw [e]
  unfold nearestIntDist
  rw [Int.fract_div_natCast_eq_div_natCast_mod]
  have hrl : v * x % q < q := Nat.mod_lt _ hq
  unfold okC at h
  have h' : pn * q ≤ pd * Nat.min (v * x % q) (q - v * x % q) := by simpa [Nat.ble_eq] using h
  have h1 : pn * q ≤ pd * (v * x % q) := le_trans h' (Nat.mul_le_mul_left pd (Nat.min_le_left _ _))
  have h2 : pn * q ≤ pd * (q - v * x % q) := le_trans h' (Nat.mul_le_mul_left pd (Nat.min_le_right _ _))
  generalize v * x % q = r at *
  apply le_min
  · rw [div_le_div_iff₀ hpd' hq']
    have : (pn : ℝ) * q ≤ pd * r := by exact_mod_cast h1
    linarith
  · have e2 : (1 : ℝ) - (r : ℝ) / q = ((q : ℝ) - r) / q := by field_simp
    rw [e2, div_le_div_iff₀ hpd' hq']
    have : (pn : ℝ) * q ≤ pd * ((q : ℝ) - r) := by
      rw [← Nat.cast_sub hrl.le]; exact_mod_cast h2
    linarith

theorem ml_ge_of_low (a b c d e pn pd x q : ℕ) (hpd : 0 < pd)
    (h : lowOK pn pd x q [a, b, c, d, e] = true) :
    (pn : ℝ) / pd ≤ ML (vecL [a, b, c, d, e]) := by
  unfold lowOK at h
  rw [Bool.and_eq_true] at h
  obtain ⟨hq, hall⟩ := h
  have hq' : 0 < q := by rw [Nat.blt_eq] at hq; exact hq
  simp only [List.all_cons, List.all_nil, Bool.and_eq_true, Bool.and_true] at hall
  obtain ⟨k0, k1, k2, k3, k4⟩ := hall
  apply KS5Tail.ML_ge_of_witness' _ ((x : ℝ) / q)
  intro i
  fin_cases i
  · simpa [vecL] using okC_real hq' hpd k0
  · simpa [vecL] using okC_real hq' hpd k1
  · simpa [vecL] using okC_real hq' hpd k2
  · simpa [vecL] using okC_real hq' hpd k3
  · simpa [vecL] using okC_real hq' hpd k4

/-! ### upper bound from a cover chain -/

def chainOK (ws : List ℕ) (pn pd L : ℕ) : ℕ → List (ℕ × ℕ) → ℕ → Bool
  | reach, [], target => Nat.ble target reach
  | reach, (w, m) :: rest, target =>
      ws.any (fun w' => Nat.beq w' w) && Nat.blt 0 w && Nat.beq (w * (L / w)) L && Nat.blt 0 L &&
        Nat.ble ((m * pd - pn) * (L / w)) reach &&
        chainOK ws pn pd L (Nat.max reach ((m * pd + pn) * (L / w))) rest target

theorem iv_close {w m pd pn L K : ℕ} (x : ℝ) (hpd : 0 < pd) (hw : 0 < w) (hK : w * K = L) (hL : 0 < L)
    (hx0 : 0 ≤ x) (hlo : (((m * pd - pn) * K : ℕ) : ℝ) ≤ x) (hhi : x ≤ (((m * pd + pn) * K : ℕ) : ℝ)) :
    nearestIntDist ((w : ℝ) * (x / (pd * L))) ≤ (pn : ℝ) / pd := by
  have hK0 : 0 < K := by
    rcases Nat.eq_zero_or_pos K with h | h
    · rw [h] at hK; omega
    · exact h
  have hP : (0 : ℝ) < pd := by exact_mod_cast hpd
  have hKr : (0 : ℝ) < K := by exact_mod_cast hK0
  have hwr : (0 : ℝ) < w := by exact_mod_cast hw
  have hPK : 0 < (pd : ℝ) * K := mul_pos hP hKr
  have hLr : (L : ℝ) = (w : ℝ) * K := by rw [← hK]; push_cast; ring
  have e0 : (w : ℝ) * (x / (pd * L)) = x / (pd * K) := by
    rw [hLr]; field_simp
  rw [e0]
  refine le_trans (nearestIntDist_le_dist _ (m : ℤ)) ?_
  have e1 : x / (pd * K) - ((m : ℤ) : ℝ) = (x - m * pd * K) / (pd * K) := by
    push_cast; field_simp
  have e2 : (pn : ℝ) / pd = (pn * K) / (pd * K) := by field_simp
  rw [e1, e2, abs_div, abs_of_pos hPK]
  apply (div_le_div_iff_of_pos_right hPK).mpr
  have hhi' : x ≤ ((m : ℝ) * pd + pn) * K := by push_cast at hhi; linarith
  have hlo' : ((m : ℝ) * pd - pn) * K ≤ x := by
    by_cases hmp : pn ≤ m * pd
    · rw [Nat.cast_mul, Nat.cast_sub hmp] at hlo
      push_cast at hlo
      linarith
    · have h0 : m * pd - pn = 0 := Nat.sub_eq_zero_of_le (by omega)
      have hlt : (m : ℝ) * pd < pn := by exact_mod_cast (by omega : m * pd < pn)
      nlinarith
  rw [abs_le]
  constructor <;> nlinarith

theorem chainOK_spec (ws : List ℕ) (pn pd L : ℕ) (hpd : 0 < pd) :
    ∀ (ch : List (ℕ × ℕ)) (reach target : ℕ), chainOK ws pn pd L reach ch target = true →
      (∀ x : ℝ, 0 ≤ x → x ≤ reach → ∃ w ∈ ws, nearestIntDist ((w : ℝ) * (x / (pd * L))) ≤ (pn : ℝ) / pd) →
      ∀ x : ℝ, 0 ≤ x → x ≤ target → ∃ w ∈ ws, nearestIntDist ((w : ℝ) * (x / (pd * L))) ≤ (pn : ℝ) / pd := by
  intro ch
  induction ch with
  | nil =>
    intro reach target h hinv x hx0 hx
    simp only [chainOK, Nat.ble_eq] at h
    exact hinv x hx0 (le_trans hx (by exact_mod_cast h))
  | cons p rest ih =>
    intro reach target h hinv
    obtain ⟨w, m⟩ := p
    simp only [chainOK, Bool.and_eq_true, List.any_eq_true, Nat.beq_eq, Nat.blt_eq, Nat.ble_eq] at h
    obtain ⟨⟨⟨⟨⟨⟨w', hw'mem, hw'⟩, hw0⟩, hwK⟩, hL⟩, hlo⟩, hrest⟩ := h
    have hwmem : w ∈ ws := by
      have : w' = w := by simpa using hw'
      rw [← this]; exact hw'mem
    refine ih _ target hrest ?_
    intro x hx0 hxr
    by_cases hxe : x ≤ reach
    · exact hinv x hx0 hxe
    · rw [not_le] at hxe
      refine ⟨w, hwmem, ?_⟩
      have hmax : (((Nat.max reach ((m * pd + pn) * (L / w)) : ℕ)) : ℝ) =
          max (reach : ℝ) (((m * pd + pn) * (L / w) : ℕ) : ℝ) := by push_cast; rfl
      rw [hmax] at hxr
      have hxhi : x ≤ (((m * pd + pn) * (L / w) : ℕ) : ℝ) := by
        rcases le_max_iff.mp hxr with h1 | h1
        · exact absurd h1 (not_le.mpr hxe)
        · exact h1
      have hxlo : (((m * pd - pn) * (L / w) : ℕ) : ℝ) ≤ x := by
        have : (((m * pd - pn) * (L / w) : ℕ) : ℝ) ≤ (reach : ℝ) := by exact_mod_cast hlo
        linarith
      exact iv_close x hpd (Nat.pos_of_ne_zero (by omega)) hwK hL hx0 hxlo hxhi

theorem gap_le_of_idx (v : Fin 5 → ℤ) (t c : ℝ) (i : Fin 5)
    (h : nearestIntDist ((v i : ℝ) * (t - ⌊t⌋)) ≤ c) : gap v t ≤ c := by
  refine le_trans (gap_le v t i) ?_
  have e : (v i : ℝ) * t = (v i : ℝ) * (t - ⌊t⌋) + ((v i * ⌊t⌋ : ℤ) : ℝ) := by push_cast; ring
  rw [e, nearestIntDist_add_int]
  exact h

theorem ml_le_of_chain (a b c d e pn pd L : ℕ) (ch : List (ℕ × ℕ)) (hpd : 0 < pd) (hL : 0 < L)
    (h : chainOK [a, b, c, d, e] pn pd L 0 ch (pd * L) = true) :
    ML (vecL [a, b, c, d, e]) ≤ (pn : ℝ) / pd := by
  unfold ML
  apply csSup_le (Set.range_nonempty _)
  rintro y ⟨t, rfl⟩
  have hP : (0 : ℝ) < pd := by exact_mod_cast hpd
  have hLr : (0 : ℝ) < L := by exact_mod_cast hL
  have hPL : (0 : ℝ) < (pd : ℝ) * L := mul_pos hP hLr
  have hinv : ∀ x : ℝ, 0 ≤ x → x ≤ ((0 : ℕ) : ℝ) →
      ∃ w ∈ [a, b, c, d, e], nearestIntDist ((w : ℝ) * (x / (pd * L))) ≤ (pn : ℝ) / pd := by
    intro x hx0 hx
    have hx' : x = 0 := le_antisymm (by simpa using hx) hx0
    refine ⟨a, by simp, ?_⟩
    rw [hx']
    simp only [zero_div, mul_zero]
    have : nearestIntDist 0 = 0 := by
      have := nearestIntDist_intCast 0
      simpa using this
    rw [this]; positivity
  have hcov := chainOK_spec [a, b, c, d, e] pn pd L hpd ch 0 (pd * L) h hinv
  have hu0 : 0 ≤ t - ⌊t⌋ := Int.fract_nonneg t
  have hu1 : t - ⌊t⌋ < 1 := Int.fract_lt_one t
  obtain ⟨w, hw, hwle⟩ := hcov (((pd * L : ℕ) : ℝ) * (t - ⌊t⌋)) (by positivity)
    (by push_cast; nlinarith)
  have hxu : ((((pd * L : ℕ) : ℝ) * (t - ⌊t⌋)) / (pd * L)) = t - ⌊t⌋ := by
    push_cast; field_simp
  rw [hxu] at hwle
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl | rfl
  · exact gap_le_of_idx _ t _ 0 (by simpa [vecL] using hwle)
  · exact gap_le_of_idx _ t _ 1 (by simpa [vecL] using hwle)
  · exact gap_le_of_idx _ t _ 2 (by simpa [vecL] using hwle)
  · exact gap_le_of_idx _ t _ 3 (by simpa [vecL] using hwle)
  · exact gap_le_of_idx _ t _ 4 (by simpa [vecL] using hwle)

/-- exact value from checked data: one rational time (lower bound) and one cover chain (upper bound) -/
theorem ml_eq_of_data (a b c d e pn pd x q L : ℕ) (ch : List (ℕ × ℕ)) (hpd : 0 < pd) (hL : 0 < L)
    (hlow : lowOK pn pd x q [a, b, c, d, e] = true)
    (hcov : chainOK [a, b, c, d, e] pn pd L 0 ch (pd * L) = true) :
    ML (vecL [a, b, c, d, e]) = (pn : ℝ) / pd :=
  le_antisymm (ml_le_of_chain a b c d e pn pd L ch hpd hL hcov) (ml_ge_of_low a b c d e pn pd x q hpd hlow)

end L5W

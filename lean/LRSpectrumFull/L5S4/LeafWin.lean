/-
# L5S4.LeafWin : the leaf window of the generator is sound (E11 rest), and `cdiv = Int.ceil`

Stage S4 block 3.  `cert.rs::leaf_info` computes, for a leaf node with Gram minors `G_0..G_3` and stage values
`c_1, c_2, c_3` (witnesses of `M(L_k)`), `m_0 = 3/10`, `m_k = c_k - 1/5`:

    den_k = 4 m_k² - ∑_{i=k+1}^{3} G_{i-1}/G_i,   hi = min { 1/den_k : den_k > 0 },
    lo    = max (ρ μ_3², ρ μ_2² - μ_3²/4, ρ μ_1² - (μ_2² + μ_3²)/4),    ρ = 3/4,    μ_i² = G_i/G_{i-1},

and the integer range `[cdiv(lo G_3), cdiv(hi G_3) - 1]` for `|v|²`.  Proved here, for the Accepted flag of a near-tight `v`
whose rows are the node rows (`ChainRep.accepted_prefix`):

* `leaf_hi_sound` : `den_k > 0  ->  μ_4² < 1/den_k` (witness-based node test at depth 4, `nodeBound_to_rat`);
* `leaf_lo_sound` : each of the three terms of `lo` is `<= μ_4²` (only `Reduced34`);
* `cdiv_eq_ceil`  : the Rust integer ceiling division `-fdiv(-a, b)` (Euclidean division, `b > 0`) equals `⌈a/b⌉`;
* `leaf_range_sound` : hence `ceil(lo G_3) <= |v|² <= ceil(hi G_3) - 1` for the Rust `lo`, `hi`.

The reindexing `∑_{i=k+1}^{3} G_{i-1}/G_i = ∑_{i<3, k<=i} G_i/G_{i+1}` between the Rust loop and the Lean `ratRHS` is
the one dictionary step stated as a definition (`denK`), not a lemma.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Radius
import LRSpectrumFull.L5S4.Window

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-- Rust `cdiv a b = -fdiv(-a, b)` (`fdiv = div_euclid`, `b > 0`) is the ceiling of `a / b`. -/
theorem cdiv_eq_ceil (a b : ℤ) (hb : 0 < b) : -((-a) / b) = ⌈(a : ℚ) / (b : ℚ)⌉ := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, b = (n : ℤ) := ⟨b.toNat, (Int.toNat_of_nonneg hb.le).symm⟩
  have h1 : (a : ℚ) / ((n : ℤ) : ℚ) = -(((-a : ℤ) : ℚ) / (n : ℚ)) := by
    push_cast; ring
  rw [h1, Int.ceil_neg]
  have := Rat.floor_intCast_div_natCast (-a) n
  rw [this]

/-- The rational `den_k` of `leaf_info` in terms of the leading Gram minors `G` (Lean form of the reindexed sum). -/
def denK (G : ℕ → ℤ) (m : ℚ) (k : ℕ) : ℚ :=
  4 * m ^ 2 - ∑ i ∈ range 3, if k ≤ i then (G i : ℚ) / (G (i + 1) : ℚ) else 0

/-- **Upper window.**  If `den_k > 0` for the witness value `c = c_k >= 1/5`, then `μ_4² < 1/den_k`. -/
theorem leaf_hi_sound {v : V5} (F : FlagData v) (hacc : Accepted F) (k : ℕ) (hk : k < 4)
    (X : V5) (W : ℤ) (hok : WitnessOk F k X W) (c : ℚ) (hcdef : c = ((wMin X W : ℤ) : ℚ) / ((W : ℤ) : ℚ))
    (hc : (1 : ℚ) / 5 ≤ c)
    (hden : 0 < denK (fun n => leadMinor (gram F) n) (c - 1 / 5) k) :
    F.Dq 3 < 1 / denK (fun n => leadMinor (gram F) n) (c - 1 / 5) k := by
  have hk4 : k < 4 := hk
  have hNB := hacc.node 4 (by omega) (by omega)
  have h := nodeBound_to_rat F 4 (by omega) (le_refl 4) hNB k hk4 X W hok c hcdef hc
  have hCq : Cq 4 = 1 := by simp [Cq]
  have hD3 : F.Dq 3 = (leadMinor (gram F) 4 : ℚ) / (leadMinor (gram F) 3 : ℚ) := Dq_minors_thm v F 3
  have hpos : 0 < F.Dq 3 := F.hDpos 3
  have hG3 : (0 : ℚ) < (leadMinor (gram F) 3 : ℚ) := by exact_mod_cast leadMinor_pos' F 3
  have hG4 : (0 : ℚ) < (leadMinor (gram F) 4 : ℚ) := by exact_mod_cast leadMinor_pos' F 4
  unfold ratRHS at h
  rw [hCq, one_mul] at h
  have h43 : (4 - 1 : ℕ) = 3 := rfl
  rw [h43] at h
  unfold denK at hden ⊢
  set S := ∑ i ∈ range 3, if k ≤ i then (leadMinor (gram F) i : ℚ) / (leadMinor (gram F) (i + 1) : ℚ) else 0
    with hS
  have hlt : 4 * (c - 1 / 5) ^ 2 - S < (leadMinor (gram F) 3 : ℚ) / (leadMinor (gram F) 4 : ℚ) := by
    have : S = ∑ i ∈ range 3, if k ≤ i then (leadMinor (gram F) i : ℚ) / (leadMinor (gram F) (i + 1) : ℚ) else 0 := rfl
    linarith
  have hinv : (leadMinor (gram F) 3 : ℚ) / (leadMinor (gram F) 4 : ℚ) = 1 / F.Dq 3 := by
    rw [hD3]; field_simp
  rw [hinv] at hlt
  rw [lt_div_iff₀ hden]
  have := (lt_div_iff₀ hpos).1 hlt
  linarith

/-- **Lower window.**  The three terms of the Rust `lo` (`ρ = 3/4`) are at most `μ_4²` for a `Reduced34` flag. -/
theorem leaf_lo_sound {v : V5} (F : FlagData v) (hr : Reduced34 F) :
    (3 / 4 : ℚ) * F.Dq 2 ≤ F.Dq 3 ∧
    (3 / 4 : ℚ) * F.Dq 1 - (1 / 4) * F.Dq 2 ≤ F.Dq 3 ∧
    (3 / 4 : ℚ) * F.Dq 0 - (1 / 4) * (F.Dq 1 + F.Dq 2) ≤ F.Dq 3 := by
  have h0 := hr 0
  have h1 := hr 1
  have h2 := hr 2
  simp only [Fin.castSucc_zero, Fin.succ_zero_eq_one] at h0
  have h1' : (3 / 4 : ℚ) * F.Dq 1 ≤ F.Dq 2 := h1
  have h2' : (3 / 4 : ℚ) * F.Dq 2 ≤ F.Dq 3 := h2
  have h0' : (3 / 4 : ℚ) * F.Dq 0 ≤ F.Dq 1 := h0
  refine ⟨h2', ?_, ?_⟩ <;> linarith

/-- **The integer range is sound.**  For any rationals `lo ≤ μ_4² < hi` (in particular the Rust `lo`, `hi`),
`ceil(lo G_3) ≤ |v|² ≤ ceil(hi G_3) - 1`. -/
theorem leaf_range_sound {v : V5} (F : FlagData v) (hv : Primitive v) (lo hi : ℚ)
    (hlo : lo ≤ F.Dq 3) (hhi : F.Dq 3 < hi) :
    ⌈lo * (leadMinor (gram F) 3 : ℚ)⌉ ≤ dot v v ∧ dot v v ≤ ⌈hi * (leadMinor (gram F) 3 : ℚ)⌉ - 1 :=
  (window_range_iff F hv lo hi).1 ⟨hlo, hhi⟩

end L5S4
end LRSpectrumFull

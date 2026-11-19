/-
# L5S4.LeafRange : `LeafWinMem` is the integer range of `leaf_info`

Case-tree certificate, part 4.  `leafLo G` is the `lo = max(l2, l1, l0)` of `leaf_window` at `ρ = 3/4`,
`leafHi` the `hi = min_{den_k > 0} 1/den_k`; `leafWinMem_iff` : the integers `n` of the window `LeafWinMem n3` are exactly
`[⌈lo G_3⌉, ⌈hi G_3⌉ - 1]` (the range the generator stores and the checker compares with a class range).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.Induct

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-- `lo` of `leaf_window` at `ρ = 3/4`, in the leading Gram minors `G`. -/
def leafLo (G : ℕ → ℤ) : ℚ :=
  max (max ((3 / 4) * ((G 3 : ℚ) / (G 2 : ℚ))) ((3 / 4) * ((G 2 : ℚ) / (G 1 : ℚ)) - (1 / 4) * ((G 3 : ℚ) / (G 2 : ℚ))))
    ((3 / 4) * ((G 1 : ℚ) / (G 0 : ℚ)) - (1 / 4) * ((G 2 : ℚ) / (G 1 : ℚ) + (G 3 : ℚ) / (G 2 : ℚ)))

/-- The stages `k < 4` with `den_k > 0`. -/
def leafKset (G : ℕ → ℤ) (c : ℕ → ℚ) : Finset ℕ := (range 4).filter (fun k => 0 < denK G (c k - 1 / 5) k)

/-- `hi` of `leaf_window` (nonempty for a noncritical leaf: `den_3 = 4 m_3² > 0`). -/
noncomputable def leafHi (G : ℕ → ℤ) (c : ℕ → ℚ) (hK : (leafKset G c).Nonempty) : ℚ :=
  (leafKset G c).inf' hK (fun k => 1 / denK G (c k - 1 / 5) k)

theorem leafWinMem_iff (n3 : NodeW 3 2) (hG : 0 < Gm n3.rows 3)
    (hK : (leafKset (fun i => Gm n3.rows i) (fun k => cOf (n3.wit k))).Nonempty) (n : ℤ) :
    LeafWinMem n3 n ↔
      ⌈leafLo (fun i => Gm n3.rows i) * (Gm n3.rows 3 : ℚ)⌉ ≤ n ∧
        n ≤ ⌈leafHi (fun i => Gm n3.rows i) (fun k => cOf (n3.wit k)) hK * (Gm n3.rows 3 : ℚ)⌉ - 1 := by
  rw [← range_iff _ _ (Gm n3.rows 3) n hG]
  unfold LeafWinMem leafLo leafHi leafKset
  simp only [max_le_iff, Finset.lt_inf'_iff, Finset.mem_filter, Finset.mem_range, and_imp]
  constructor
  · rintro ⟨h1, h2, h3, h4⟩
    exact ⟨⟨⟨h1, h2⟩, h3⟩, fun k hk hden => h4 k hk hden⟩
  · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩
    exact ⟨h1, h2, h3, fun k hk hden => h4 k hk hden⟩

end L5S4
end LRSpectrumFull

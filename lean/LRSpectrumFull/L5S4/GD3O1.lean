/-
# L5S4.GD3O1 : flat class-table cover check `t4F` and its bridge to `T4Cover` (stage S4 block 15, part 1)

`T4Cover C recs` (GD3K4): every class-kind leaf record (kind not 0, not 1) has a class in `C.t4` whose rows are the record's
class rows `r.cl` and whose range list contains the record's window range.

Flat form.  The record accessor `g : ℕ → ℤ` (32-bit digits of one natural) carries, after the 97 fixed digits (no pair-reduction
steps), one more digit: the class id `cidOf g` into a local class table.  The table is ONE natural `TT` (digits `tg`),
stride `S`: digits `S c + 0..14` the three rows of the class representative, `S c + 15` the number of merged ranges,
`S c + 16 + 2 t`, `S c + 17 + 2 t` the range `[lo, hi]`.  `t4F` is a plain `Int` comparison: 15 digit equalities and a
range scan.  `t4F_sound` : `t4F tg S nT g = true` gives the `T4Cover` clause for `recOf g` against the table
`(List.range nT).map (t4At tg S)`.

`LocRegistered C tab` says that a global certificate `C` registers every local class (same rows, ranges covered);
`leafRelW_of_registered` lifts `LeafRelW` from the local certificate to `C`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3F1

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

def t4Row (tg : ℕ → ℤ) (base : ℕ) : V5 := fun a => tg (base + a.val)

def t4Rng (tg : ℕ → ℤ) (S c : ℕ) : List (ℤ × ℤ) :=
  (List.range (tg (S * c + 15)).toNat).map fun t => (tg (S * c + 16 + 2 * t), tg (S * c + 17 + 2 * t))

/-- the table entry `c` as a `T4Rec` (only `l` and `ranges` are read by `T4Cover`; `g, k, q, p` are placeholders to be filled by the lines stage). -/
def t4At (tg : ℕ → ℤ) (S c : ℕ) : T4Rec where
  g := SP.one
  l := fun i => t4Row tg (S * c + 5 * i.val)
  k := fun _ _ => 0
  q := fun _ _ => 0
  p := fun _ _ => 0
  ranges := t4Rng tg S c

def cidOf (g : ℕ → ℤ) : ℕ := (g (97 + 3 * (g 96).toNat)).toNat

def eq5 (g tg : ℕ → ℤ) (o p : ℕ) : Bool :=
  decide (g o = tg p) && decide (g (o + 1) = tg (p + 1)) && decide (g (o + 2) = tg (p + 2)) &&
    decide (g (o + 3) = tg (p + 3)) && decide (g (o + 4) = tg (p + 4))

def t4F (tg : ℕ → ℤ) (S nT : ℕ) (g : ℕ → ℤ) : Bool :=
  decide (g 49 ≤ 1) ||
  (decide (cidOf g < nT) && eq5 g tg 81 (S * cidOf g) && eq5 g tg 86 (S * cidOf g + 5) &&
    eq5 g tg 91 (S * cidOf g + 10) &&
    (List.range (tg (S * cidOf g + 15)).toNat).any fun t =>
      decide (tg (S * cidOf g + 16 + 2 * t) ≤ g 51) && decide (g 52 ≤ tg (S * cidOf g + 17 + 2 * t)))

theorem eq5_sound (g tg : ℕ → ℤ) (o p : ℕ) (h : eq5 g tg o p = true) (a : Fin 5) : g (o + a.val) = tg (p + a.val) := by
  unfold eq5 at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩ := h
  rcases a with ⟨v, hv⟩
  match v, hv with
  | 0, _ => simpa using h0
  | 1, _ => simpa using h1
  | 2, _ => simpa using h2
  | 3, _ => simpa using h3
  | 4, _ => simpa using h4

theorem t4F_sound (tg : ℕ → ℤ) (S nT : ℕ) (g : ℕ → ℤ) (h : t4F tg S nT g = true)
    (hk0 : (recOf g).kind ≠ 0) (hk1 : (recOf g).kind ≠ 1) :
    ∃ cl ∈ (List.range nT).map (t4At tg S), (∀ i : Fin 4, i.val < 3 → padL3 cl.l i = rowsL (recOf g).cl i) ∧
      ∃ rg ∈ cl.ranges, rg.1 ≤ (recOf g).rlo ∧ (recOf g).rhi ≤ rg.2 := by
  have hk : 1 < g 49 := by
    have e0 : (g 49).toNat ≠ 0 := hk0
    have e1 : (g 49).toNat ≠ 1 := hk1
    omega
  unfold t4F at h
  simp only [Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, List.any_eq_true] at h
  rcases h with h | ⟨⟨⟨⟨hc, e0⟩, e1⟩, e2⟩, t, ht, hlo, hhi⟩
  · omega
  · refine ⟨t4At tg S (cidOf g), List.mem_map.2 ⟨cidOf g, List.mem_range.2 hc, rfl⟩, ?_, ?_⟩
    · intro i hi
      funext a
      have hi3 : i.val < 3 := hi
      rcases i with ⟨iv, hiv⟩
      match iv, hiv, hi3 with
      | 0, _, _ => simpa [padL3, t4At, t4Row, rowsL, recOf, v5g] using (eq5_sound g tg 81 (S * cidOf g) e0 a).symm
      | 1, _, _ => simpa [padL3, t4At, t4Row, rowsL, recOf, v5g] using (eq5_sound g tg 86 (S * cidOf g + 5) e1 a).symm
      | 2, _, _ => simpa [padL3, t4At, t4Row, rowsL, recOf, v5g] using (eq5_sound g tg 91 (S * cidOf g + 10) e2 a).symm
    · exact ⟨(tg (S * cidOf g + 16 + 2 * t), tg (S * cidOf g + 17 + 2 * t)),
        List.mem_map.2 ⟨t, ht, rfl⟩, hlo, hhi⟩

def LocRegistered (C : Certificate) (tab : List T4Rec) : Prop :=
  ∀ cl ∈ tab, ∃ cl' ∈ C.t4, cl'.l = cl.l ∧ ∀ rg ∈ cl.ranges, ∃ rg' ∈ cl'.ranges, rg'.1 ≤ rg.1 ∧ rg.2 ≤ rg'.2

theorem leafRelW_of_registered {C : Certificate} {tab : List T4Rec} {n3 : LeafW}
    (hsub : LocRegistered C tab) (h : LeafRelW ⟨[], [], [], [], tab, []⟩ n3) : LeafRelW C n3 := by
  refine ⟨h.1, fun hne hw => ?_⟩
  obtain ⟨cl, hcl, hmap, rg, hrg, hrng⟩ := h.2 hne hw
  obtain ⟨cl', hcl', hl, hr⟩ := hsub cl hcl
  obtain ⟨rg', hrg', h1, h2⟩ := hr rg hrg
  refine ⟨cl', hcl', ?_, rg', hrg', fun n hn => ?_⟩
  · rw [hl]; exact hmap
  · obtain ⟨a, b⟩ := hrng n hn
    exact ⟨le_trans h1 a, le_trans b h2⟩

end L5S4
end LRSpectrumFull

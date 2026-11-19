/-
# L5S4.GD3K2 : chunked list completeness for the depth-3 child step (stage S4 block 11)

The data of one depth-3 node is split into CHUNKS `(t0, t1 start, number of rows, data)` (consecutive rows of one group `t0`),
each checked by its own `rowsOk` theorem in its own module (kernel memory is proportional to the work inside one theorem).
The chunk data is a packed Nat of 16-bit digits (`unpackL`; no soundness is needed for the decoder because the Boolean
`rowsOk` is evaluated on the decoded list itself).

* `coverOk`, `rowKeys`, `rowKeys_mem` : the chunks tile every row `(t0, t1)` of the ball box (a cheap structural Boolean);
* `child_list_complete3k` : for EVERY node `n : NodeW 2 3` (generic `a22_pos`, `hrad` from `hrad_of_ok`), if the chunks tile
  the rows and each chunk passes `rowsOk`, every `y` with `ChildPass n y` has its triple `(t0, t1, t2)` in `storedOf cks`;
* `AllOk`, `allOk_mem` : the per-chunk theorems assembled into the hypothesis `hall`.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3K1

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

deriving instance DecidableEq for FC3

abbrev Chunk := ℤ × ℤ × ℕ × List ℤ

/-- decode `len` 16-bit digits of `N` (biased by 32768), lowest digit first. -/
def unpackL : ℕ → ℕ → List ℤ
  | _, 0 => []
  | N, k + 1 => (((N % 65536 : ℕ) : ℤ) - 32768) :: unpackL (N / 65536) k

def rowKeys (f : FC3) : List (ℤ × ℤ) :=
  (List.range (f.T0 + 1).toNat).flatMap fun k : ℕ =>
    (List.range (nRows f (k : ℤ))).map fun j : ℕ => ((k : ℤ), firstT1 f (k : ℤ) + (j : ℤ))

def inChunk (c : Chunk) (k : ℤ × ℤ) : Bool :=
  decide (c.1 = k.1) && decide (c.2.1 ≤ k.2) && decide (k.2 < c.2.1 + (c.2.2.1 : ℤ))

def coverOk (f : FC3) (cks : List Chunk) : Bool := (rowKeys f).all fun k => cks.any fun c => inChunk c k

def storedOf (cks : List Chunk) : List (ℤ × ℤ × ℤ) :=
  cks.flatMap fun c => (rowsPairs c.2.2.1 c.2.1 c.2.2.2).map fun p => (c.1, p.1, p.2)

theorem rowKeys_mem (f : FC3) (t0 t1 : ℤ) (h0 : 0 ≤ t0) (h0' : t0 ≤ f.T0) (h1 : firstT1 f t0 ≤ t1)
    (h1' : t1 < firstT1 f t0 + (nRows f t0 : ℤ)) : (t0, t1) ∈ rowKeys f := by
  have e : ((t0.toNat : ℕ) : ℤ) = t0 := Int.toNat_of_nonneg h0
  unfold rowKeys
  rw [List.mem_flatMap]
  refine ⟨t0.toNat, ?_, ?_⟩
  · rw [List.mem_range]; omega
  · rw [List.mem_map]
    rw [e]
    refine ⟨(t1 - firstT1 f t0).toNat, ?_, ?_⟩
    · rw [List.mem_range]; omega
    · refine Prod.ext rfl ?_
      show firstT1 f t0 + ((t1 - firstT1 f t0).toNat : ℤ) = t1
      omega

@[reducible] def AllOk (f : FC3) : List Chunk → Prop
  | [] => True
  | c :: cs => rowsOk f c.1 c.2.2.1 c.2.1 c.2.2.2 = true ∧ AllOk f cs

theorem allOk_mem (f : FC3) : ∀ (cs : List Chunk), AllOk f cs → ∀ c ∈ cs, rowsOk f c.1 c.2.2.1 c.2.1 c.2.2.2 = true
  | [], _, c, hc => absurd hc List.not_mem_nil
  | d :: cs, h, c, hc => by
      rcases List.mem_cons.1 hc with rfl | hc
      · exact h.1
      · exact allOk_mem f cs h.2 c hc

/-- **Chunked list completeness at depth 3, every node.** -/
theorem child_list_complete3k (n : NodeW 2 3) (bn bd : ℤ) (hbd : 0 < bd)
    (hrad : radFrac (Cq (2 + 1)) n.wit n.rows 2 n.rk = (bn : ℚ) / bd) (cks : List Chunk)
    (hcov : coverOk (FC3.ofNode n bn bd) cks = true) (hall : AllOk (FC3.ofNode n bn bd) cks)
    (y : V5) (hp : ChildPass n y) :
    ∃ e ∈ storedOf cks, e = (tvec n.b y 0, tvec n.b y 1, tvec n.b y 2) := by
  have ha := a22_pos n bn bd
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
  have hlo : firstT1 (FC3.ofNode n bn bd) (tvec n.b y 0) ≤ tvec n.b y 1 ∧
      tvec n.b y 1 < firstT1 (FC3.ofNode n bn bd) (tvec n.b y 0) + (nRows (FC3.ofNode n bn bd) (tvec n.b y 0) : ℤ) := by
    unfold firstT1 nRows
    by_cases hz : tvec n.b y 0 = 0
    · rw [if_pos hz, if_pos hz]
      have := hf1 hz
      omega
    · rw [if_neg hz, if_neg hz]
      omega
  have hk : (tvec n.b y 0, tvec n.b y 1) ∈ rowKeys (FC3.ofNode n bn bd) :=
    rowKeys_mem _ _ _ hf0 (by omega) hlo.1 hlo.2
  unfold coverOk at hcov
  rw [List.all_eq_true] at hcov
  have hc1 := hcov _ hk
  rw [List.any_eq_true] at hc1
  obtain ⟨c, hc, hic⟩ := hc1
  unfold inChunk at hic
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hic
  obtain ⟨⟨h1, h2⟩, h3⟩ := hic
  have hmem := rowsOk_mem (FC3.ofNode n bn bd) ha hbd c.1 c.2.2.1 c.2.1 c.2.2.2 (allOk_mem _ cks hall c hc)
    (tvec n.b y 1) (tvec n.b y 2) h2 h3 (by rw [h1]; exact hFv)
    (fun h0 h1' => hf2 (by rw [← h1]; exact h0) h1') (by rw [h1]; exact hpp)
  refine ⟨(c.1, tvec n.b y 1, tvec n.b y 2), ?_, by rw [h1]⟩
  unfold storedOf
  rw [List.mem_flatMap]
  exact ⟨c, hc, List.mem_map.2 ⟨(tvec n.b y 1, tvec n.b y 2), hmem, rfl⟩⟩

end L5S4
end LRSpectrumFull

/-
# L5S4.GD3K6 : helpers of the split leaf-record layout (stage S4 block 13)

* `unpackL32` : 32-bit-digit variant of `unpackL` (leaf records of the larger representatives have entries above 2^15).
* `parseAll_length` : `parseAll k z` has exactly `k` records.
* `forall_of_chunks` : a property of every element of a list follows from the same property of consecutive chunks of
  length `P` (used to split the leaf-record check `recs_ok` into small kernel computations).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3K4

namespace LRSpectrumFull
namespace L5S4

/-- decode `len` 32-bit digits of `N` (biased by 2^31), lowest digit first. -/
def unpackL32 : ℕ → ℕ → List ℤ
  | _, 0 => []
  | N, k + 1 => (((N % 4294967296 : ℕ) : ℤ) - 2147483648) :: unpackL32 (N / 4294967296) k

theorem parseAll_length (k : ℕ) (z : List ℤ) : (parseAll k z).length = k := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih => simp [parseAll, ih]

theorem forall_of_chunks {α : Type} (p : α → Prop) (l : List α) (P n : ℕ) (hP : 0 < P)
    (hl : l.length ≤ n * P) (h : ∀ j < n, ∀ r ∈ (l.drop (j * P)).take P, p r) : ∀ r ∈ l, p r := by
  intro r hr
  obtain ⟨i, hi, hir⟩ := List.mem_iff_getElem.mp hr
  have hj : i / P < n := by
    rw [Nat.div_lt_iff_lt_mul hP]
    exact lt_of_lt_of_le hi hl
  apply h (i / P) hj
  have hdm : P * (i / P) + i % P = i := Nat.div_add_mod i P
  have hmod : i % P < P := Nat.mod_lt _ hP
  have hjP : i / P * P = P * (i / P) := Nat.mul_comm _ _
  rw [List.mem_iff_getElem]
  have hlen : i % P < ((l.drop (i / P * P)).take P).length := by
    simp only [List.length_take, List.length_drop]
    omega
  refine ⟨i % P, hlen, ?_⟩
  rw [List.getElem_take, List.getElem_drop]
  subst hir
  congr 1
  omega

end L5S4
end LRSpectrumFull

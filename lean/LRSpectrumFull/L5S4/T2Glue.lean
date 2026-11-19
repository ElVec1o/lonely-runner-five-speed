/-
# L5S4.T2Glue : list lemmas for the generated per-node `t2` modules (stage S4R)

* `forall_getD` : a property of `L.getD i d` for every `i < L.length` is a property of every member.
* `all_of_chunks` : a Boolean test passed on the consecutive blocks `(L.drop (k*c)).take c` (k below the ceiling of
  `L.length / c`) is passed on every member of `L` (the kernel checks one block per theorem, which bounds its memory).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.T2Gen

namespace LRSpectrumFull
namespace L5S4

theorem forall_getD {α : Type} (L : List α) (d : α) {Q : α → Prop}
    (h : ∀ i, i < L.length → Q (L.getD i d)) : ∀ x ∈ L, Q x := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := h i hi
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] using this

theorem all_of_chunks (L : List ℕ) (c : ℕ) (hc : 0 < c) (Q : ℕ → Bool)
    (h : ∀ k, k < (L.length + c - 1) / c → ((L.drop (k * c)).take c).all Q = true) :
    ∀ N ∈ L, Q N = true := by
  intro N hN
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hN
  have h1 : (i + c) / c ≤ (L.length + c - 1) / c := Nat.div_le_div_right (by omega)
  have h2 : (i + c) / c = i / c + 1 := Nat.add_div_right i hc
  have hk : i / c < (L.length + c - 1) / c := by omega
  have hq := Nat.div_add_mod' i c
  have hm := Nat.mod_lt i hc
  have e : ((L.drop (i / c * c)).take c)[i % c]? = some L[i] := by
    rw [List.getElem?_take_of_lt hm, List.getElem?_drop]
    have : i / c * c + i % c = i := hq
    rw [this]
    simp [List.getElem?_eq_getElem hi]
  have hmem : L[i] ∈ (L.drop (i / c * c)).take c := List.mem_of_getElem? e
  exact (List.all_eq_true.1 (h (i / c) hk)) _ hmem

end L5S4
end LRSpectrumFull

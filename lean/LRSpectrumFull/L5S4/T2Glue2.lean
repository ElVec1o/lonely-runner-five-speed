/-
# L5S4.T2Glue2 : chunked leader coverage for the generated per-node `t2` modules (stage S4S)

The final module of a depth-1 node used to evaluate `unpackRec` and `dedup` over ALL stored records inside single theorems
(`lead` by `List.dedup`, `hlead` and the `lead` control by `decide`); the kernel memory of a theorem grows with the work done in
it, and the final module of the big nodes passed 8 GB.  The fix keeps every theorem at the size of one block of records:

* `leadOk lead N` : the class representative position (digit 45 of the packed record `N`) is a member of the literal list `lead`;
* `hlead_of_chunks` : if `leadOk lead` holds on each block `(L.drop (k*c)).take c`, `k < n` with `n = ceil (L.length / c)`,
  then `cRep (unpackRec N) ∈ lead` for every member `N` of `L` (this is the hypothesis `hlead` of `t2_lead` / `t2_of_link`).

Only digit 45 is read; `lead` is emitted by the generator as a literal, so nothing is unpacked or deduplicated in the kernel.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.T2Glue

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-- the class representative position of the packed record `N` (digit 45) lies in `lead` -/
def leadOk (lead : List ℕ) (N : ℕ) : Bool := lead.contains (dgI N 45).toNat

theorem hlead_of_chunks (L lead : List ℕ) (c : ℕ) (hc : 0 < c) (n : ℕ) (hn : (L.length + c - 1) / c = n)
    (h : ∀ k, k < n → ((L.drop (k * c)).take c).all (leadOk lead) = true) :
    ∀ N ∈ L, cRep (unpackRec N) ∈ lead := by
  intro N hN
  have h1 : leadOk lead N = true := all_of_chunks L c hc (leadOk lead) (fun k hk => h k (hn ▸ hk)) N hN
  have hrep : cRep (unpackRec N) = (dgI N 45).toNat := by
    unfold cRep; rw [unpack_getD N 45 (by norm_num)]
  rw [hrep]
  unfold leadOk at h1
  exact List.contains_iff_mem.1 h1

end L5S4
end LRSpectrumFull

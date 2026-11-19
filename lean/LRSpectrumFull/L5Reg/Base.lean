/-
# L5Reg.Base : registration of the per-rep local class tables in the lines class table (H8, stage S4T)

The leaf side (`GD3O<c>`) proves `t3` under `LocRegistered C tabO`: every local class has a class of `C.t4` with the same rows `l` and covering ranges.
For `C = lineCert B t5` the class table is `linTab B` (records of the lines chunks), so registration of the local table of a rep is a finite check
against the lines records.  `regChk tg S c N` compares the local class `c` (digits `tg`, stride `S`) with the lines record `N`: the 15 row digits
are equal and every local range lies inside a record range.  `regAll` runs `regChk` over the local table with ADVICE (chunk, index) per class
(the lookup is by chunk offset in a list of at most 1000 records, never `getD` on the whole table); the advice is untrusted, the kernel checks it.
`locReg_of_adv` : a passing `regAll` plus `p ∈ chunk -> p ∈ B` for the chunks used gives `LocRegistered (lineCert B t5)` of the local table.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.LinRCov
import LRSpectrumFull.L5S4.GD3O1

namespace LRSpectrumFull
namespace L5Reg

open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S4.Lin

/-- local class `c` of the table `(tg, S)` against the lines record `N`: rows equal, every local range inside a record range. -/
def regChk (tg : ℕ → ℤ) (S c N : ℕ) : Bool :=
  (List.range 15).all (fun k => decide (tg (S * c + k) = Lin.dg N (11 + k))) &&
  (List.range (tg (S * c + 15)).toNat).all (fun t =>
    (List.range (Lin.dg N 61).toNat).any (fun j =>
      decide (Lin.dg N (62 + 2 * j) ≤ tg (S * c + 16 + 2 * t)) && decide (tg (S * c + 17 + 2 * t) ≤ Lin.dg N (63 + 2 * j))))

theorem regChk_sound (tg : ℕ → ℤ) (S c N : ℕ) (h : regChk tg S c N = true) :
    (t4At tg S c).l = (t4OfRec N).l ∧
    ∀ rg ∈ (t4At tg S c).ranges, ∃ rg' ∈ (t4OfRec N).ranges, rg'.1 ≤ rg.1 ∧ rg.2 ≤ rg'.2 := by
  unfold regChk at h
  rw [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  rw [List.all_eq_true] at h1 h2
  refine ⟨?_, ?_⟩
  · funext i a
    have hi := i.isLt
    have ha := a.isLt
    have hk := decide_eq_true_iff.1 (h1 (5 * i.val + a.val) (List.mem_range.2 (by omega)))
    show tg (S * c + 5 * i.val + a.val) = Lin.dg N (11 + 5 * i.val + a.val)
    rw [show S * c + 5 * i.val + a.val = S * c + (5 * i.val + a.val) by omega,
      show 11 + 5 * i.val + a.val = 11 + (5 * i.val + a.val) by omega]
    exact hk
  · intro rg hrg
    have hrg' : rg ∈ (List.range (tg (S * c + 15)).toNat).map
        (fun t => (tg (S * c + 16 + 2 * t), tg (S * c + 17 + 2 * t))) := hrg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hrg'
    obtain ⟨j, hj, hjj⟩ := List.any_eq_true.1 (h2 t ht)
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hjj
    exact ⟨(Lin.dg N (62 + 2 * j), Lin.dg N (63 + 2 * j)), List.mem_map.2 ⟨j, hj, rfl⟩, hjj.1, hjj.2⟩

/-- chunk lookup by key (`bls` lists the chunks a rep uses; the other keys give the empty list). -/
def assoc (bls : List (ℕ × List (ℕ × ℕ))) (j : ℕ) : List (ℕ × ℕ) :=
  match bls.find? (fun e => e.1 == j) with
  | some e => e.2
  | none => []

theorem assoc_mem {bls : List (ℕ × List (ℕ × ℕ))} {j : ℕ} {p : ℕ × ℕ} (h : p ∈ assoc bls j) :
    ∃ e ∈ bls, p ∈ e.2 := by
  unfold assoc at h
  split at h
  · rename_i e he
    exact ⟨e, List.mem_of_find?_eq_some he, h⟩
  · simp at h

def regChk' (tg : ℕ → ℤ) (S c : ℕ) (bl : List (ℕ × ℕ)) (k : ℕ) : Bool :=
  match bl[k]? with
  | some p => regChk tg S c p.1
  | none => false

def regAll (tg : ℕ → ℤ) (S : ℕ) (bl : ℕ → List (ℕ × ℕ)) : ℕ → List (ℕ × ℕ) → Bool
  | _, [] => true
  | i, (j, k) :: r => regChk' tg S i (bl j) k && regAll tg S bl (i + 1) r

theorem regAll_sound (tg : ℕ → ℤ) (S : ℕ) (bl : ℕ → List (ℕ × ℕ)) :
    ∀ (adv : List (ℕ × ℕ)) (i0 : ℕ), regAll tg S bl i0 adv = true →
      ∀ c, i0 ≤ c → c < i0 + adv.length → ∃ j, ∃ p ∈ bl j, regChk tg S c p.1 = true := by
  intro adv
  induction adv with
  | nil => intro i0 _ c h1 h2; simp at h2; omega
  | cons a r ih =>
    intro i0 h c h1 h2
    obtain ⟨j, k⟩ := a
    unfold regAll at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h3, h4⟩ := h
    by_cases hc : c = i0
    · subst hc
      unfold regChk' at h3
      cases hb : (bl j)[k]? with
      | none => rw [hb] at h3; simp at h3
      | some p =>
        rw [hb] at h3
        exact ⟨j, p, List.mem_of_getElem? hb, h3⟩
    · exact ih (i0 + 1) h4 c (by omega) (by simp at h2; omega)

/-- **Registration of a local table from advice.** -/
theorem locReg_of_adv (tg : ℕ → ℤ) (S nT : ℕ) (bls : List (ℕ × List (ℕ × ℕ))) (B : List (ℕ × ℕ)) (t5 : List T5Rec)
    (adv : List (ℕ × ℕ)) (hl : adv.length = nT) (h : regAll tg S (assoc bls) 0 adv = true)
    (hs : ∀ e ∈ bls, ∀ p ∈ e.2, p ∈ B) :
    LocRegistered (lineCert B t5) ((List.range nT).map (t4At tg S)) := by
  intro cl hcl
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hcl
  obtain ⟨j, p, hp, hr⟩ := regAll_sound tg S (assoc bls) adv 0 h c (Nat.zero_le _) (by rw [List.mem_range] at hc; omega)
  obtain ⟨e, he, hpe⟩ := assoc_mem hp
  have hpB : p ∈ B := hs e he p hpe
  obtain ⟨hl', hrg⟩ := regChk_sound tg S c p.1 hr
  exact ⟨t4OfRec p.1, List.mem_map.2 ⟨p, hpB, rfl⟩, hl'.symm, hrg⟩

#print axioms regChk_sound
#print axioms regAll_sound
#print axioms locReg_of_adv

end L5Reg
end LRSpectrumFull

/-
# L5Reg.Equiv : registration of a local class in the lines table up to a signed permutation (H8', stage S4T)

FINDING (OBSERVED, Rust `l5reg hnftest`): the local class rows of the leaf modules (`GD3O<c>T`, rows `cl` = row-HNF of `G * (leaf rows)`) are NOT the rows `l`
(digits 11..25) of the lines record of the same class: the lines record stores the rows before the canonical map `G` (digits 1..10, `gp`/`ge`).  So the
exact-row registration `LocRegistered (lineCert B t5) tabO` of `L5Reg.Base` is false for every rep with classes; the right transfer is by the symmetry `G`.

`LinesCl t5 cl` is the lines clause of one class.  `linesCl_transfer`: if `G (l'_i) = sum_k M_ik l_k` (G a signed permutation, `M` an integer 3x3 matrix) and every range of `cl`
lies in a range of `cl'`, then `LinesCl t5 cl'` gives `LinesCl t5 cl`  (u in class cl  =>  `G^-1 u` in class cl'; primitive, nonzero, distinct absolute values and `ML` are
invariant; the exceptional tuple is moved by `G`).  `eqChk` is the decidable test of this data against a lines record `N` (the `G` is read from digits 1..10 of `N`),
`eqChk_sound` its soundness.  The advice (record, matrix) is untrusted; the kernel checks it.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.LinRCov
import LRSpectrumFull.L5S4.GD3F1
import LRSpectrumFull.L5Reg.Base

namespace LRSpectrumFull
namespace L5Reg

open LRSpectrumFull.L5S3 LRSpectrumFull.L5S4 LRSpectrumFull.L5S4.Lin

/-- the lines clause of one class (the shape produced by `Lin.lines_clause_tab`). -/
def LinesCl (t5 : List T5Rec) (cl : T4Rec) : Prop :=
  ∀ u : V5, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) → InClass cl u →
    (∃ r ∈ t5, ∃ g : SP, g.act u = r.v) ∨ 1 / 5 ≤ ML u

theorem abs_inv_act (G : SP) (u : V5) (i : Fin 5) : |G.inv.act u i| = |u (G.σ.symm i)| := by
  simp only [SP.act, SP.inv]
  rcases G.hε (G.σ.symm i) with h | h <;> rw [h] <;> simp

theorem linesCl_transfer (t5 : List T5Rec) (cl cl' : T4Rec) (G : SP) (M : Fin 3 → Fin 3 → ℤ)
    (hrow : ∀ i : Fin 3, G.act (cl'.l i) = fun a => ∑ k : Fin 3, M i k * cl.l k a)
    (hrg : ∀ rg ∈ cl.ranges, ∃ rg' ∈ cl'.ranges, rg'.1 ≤ rg.1 ∧ rg.2 ≤ rg'.2)
    (h : LinesCl t5 cl') : LinesCl t5 cl := by
  intro u hp hnz hd hin
  obtain ⟨hl, rg, hrgm, hlo, hhi⟩ := hin
  have hp' : Primitive (G.inv.act u) := primitive_act hp G.inv
  have hnz' : ∀ i, G.inv.act u i ≠ 0 := nz_act hnz G.inv
  have hd' : ∀ i j, i ≠ j → |G.inv.act u i| ≠ |G.inv.act u j| := by
    intro i j hij
    rw [abs_inv_act, abs_inv_act]
    exact hd _ _ (fun e => hij (G.σ.symm.injective e))
  have hdot : dot (G.inv.act u) (G.inv.act u) = dot u u := dot_act G.inv u u
  obtain ⟨rg', hrg', h1, h2⟩ := hrg rg hrgm
  have hin' : InClass cl' (G.inv.act u) := by
    refine ⟨fun i => ?_, rg', hrg', ?_, ?_⟩
    · have e1 : dot (cl'.l i) (G.inv.act u) = dot (G.act (cl'.l i)) u := by
        rw [← dot_act G (cl'.l i) (G.inv.act u), act_act_inv]
      rw [e1, hrow i]
      have e2 : dot (fun a => ∑ k : Fin 3, M i k * cl.l k a) u = ∑ k : Fin 3, M i k * dot (cl.l k) u := by
        unfold dot
        simp only [Finset.sum_mul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun k _ => ?_)
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun a _ => ?_)
        ring
      rw [e2]
      simp [hl]
    · rw [hdot]; omega
    · rw [hdot]; omega
  rcases h _ hp' hnz' hd' hin' with ⟨r, hr, g, hg⟩ | hml
  · exact Or.inl ⟨r, hr, g.mul G.inv, by rw [act_mul]; exact hg⟩
  · right
    rw [ML_act] at hml
    exact hml

/-- the symmetry read from digits 1..10 of a lines record. -/
def recG (N : ℕ) : ℕ → ℤ := fun k => Lin.dg N (k - 52)

/-- decidable test: `G` (digits 1..10 of `N`) is a signed permutation, `G * l'_i = sum_k M_ik l_k` for the three rows of the local class `c` (digits `tg`, stride `S`),
and every local range lies in a range of the record. -/
def eqChk (tg : ℕ → ℤ) (S c N : ℕ) (M : List ℤ) : Bool :=
  gokF (recG N) &&
  (List.range 3).all (fun i => (List.range 5).all (fun a =>
    decide (Lin.dg N (6 + a) * Lin.dg N (11 + 5 * i + (Lin.dg N (1 + a)).toNat % 5) =
      M.getD (3 * i) 0 * tg (S * c + a) + M.getD (3 * i + 1) 0 * tg (S * c + 5 + a) + M.getD (3 * i + 2) 0 * tg (S * c + 10 + a)))) &&
  (List.range (tg (S * c + 15)).toNat).all (fun t =>
    (List.range (Lin.dg N 61).toNat).any (fun j =>
      decide (Lin.dg N (62 + 2 * j) ≤ tg (S * c + 16 + 2 * t)) && decide (tg (S * c + 17 + 2 * t) ≤ Lin.dg N (63 + 2 * j))))

theorem eqChk_sound (t5 : List T5Rec) (tg : ℕ → ℤ) (S c N : ℕ) (M : List ℤ) (h : eqChk tg S c N M = true)
    (hN : LinesCl t5 (t4OfRec N)) : LinesCl t5 (t4At tg S c) := by
  unfold eqChk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hg, hrows⟩, hrng⟩ := h
  have hgok := gok_of_F (recG N) hg
  refine linesCl_transfer t5 (t4At tg S c) (t4OfRec N) (gSP (recOf (recG N)).gp hgok)
    (fun i j => M.getD (3 * i.val + j.val) 0) ?_ ?_ hN
  · intro i
    funext a
    rw [List.all_eq_true] at hrows
    have h1 := List.all_eq_true.1 (hrows i.val (List.mem_range.2 i.isLt)) a.val (List.mem_range.2 a.isLt)
    have h2 := decide_eq_true_iff.1 h1
    rw [gSP_act]
    simp only [Fin.sum_univ_three, t4At, t4Row, t4OfRec]
    have e1 : (recOf (recG N)).gp.2 a = Lin.dg N (6 + a.val) := by
      simp [recOf, recG]
      congr 1; omega
    have e2 : ((recOf (recG N)).gp.1 a).val = (Lin.dg N (1 + a.val)).toNat % 5 := by
      have h53 : 53 + a.val - 52 = 1 + a.val := by omega
      simp [recOf, recG, h53]
    rw [e1, e2]
    simpa [Fin.val_zero, Fin.val_one, Fin.val_two, mul_comm, add_comm, add_left_comm, add_assoc, Nat.add_assoc] using h2
  · intro rg hrg
    have hrg' : rg ∈ (List.range (tg (S * c + 15)).toNat).map
        (fun t => (tg (S * c + 16 + 2 * t), tg (S * c + 17 + 2 * t))) := hrg
    obtain ⟨t, ht, rfl⟩ := List.mem_map.1 hrg'
    obtain ⟨j, hj, hjj⟩ := List.any_eq_true.1 ((List.all_eq_true.1 hrng) t ht)
    rw [Bool.and_eq_true, decide_eq_true_eq, decide_eq_true_eq] at hjj
    exact ⟨(Lin.dg N (62 + 2 * j), Lin.dg N (63 + 2 * j)), List.mem_map.2 ⟨j, hj, rfl⟩, hjj.1, hjj.2⟩

def eqChk' (tg : ℕ → ℤ) (S c : ℕ) (bl : List (ℕ × ℕ)) (k : ℕ) (M : List ℤ) : Bool :=
  match bl[k]? with
  | some p => eqChk tg S c p.1 M
  | none => false

/-- `adv` lists, for the local classes `i0, i0+1, ..` in order, the lines record `(chunk, index)` and the matrix `M` (row-major 3x3). -/
def eqAll (tg : ℕ → ℤ) (S : ℕ) (bl : ℕ → List (ℕ × ℕ)) : ℕ → List (ℕ × ℕ × List ℤ) → Bool
  | _, [] => true
  | i, (j, k, M) :: r => eqChk' tg S i (bl j) k M && eqAll tg S bl (i + 1) r

theorem eqAll_sound (t5 : List T5Rec) (tg : ℕ → ℤ) (S : ℕ) (bl : ℕ → List (ℕ × ℕ))
    (hbl : ∀ j, ∀ p ∈ bl j, LinesCl t5 (t4OfRec p.1)) :
    ∀ (adv : List (ℕ × ℕ × List ℤ)) (i0 : ℕ), eqAll tg S bl i0 adv = true →
      ∀ c, i0 ≤ c → c < i0 + adv.length → LinesCl t5 (t4At tg S c) := by
  intro adv
  induction adv with
  | nil => intro i0 _ c h1 h2; simp at h2; omega
  | cons a r ih =>
    intro i0 h c h1 h2
    obtain ⟨j, k, M⟩ := a
    unfold eqAll at h
    rw [Bool.and_eq_true] at h
    obtain ⟨h3, h4⟩ := h
    by_cases hc : c = i0
    · subst hc
      unfold eqChk' at h3
      cases hb : (bl j)[k]? with
      | none => rw [hb] at h3; simp at h3
      | some p =>
        rw [hb] at h3
        exact eqChk_sound t5 tg S c p.1 M h3 (hbl j p (List.mem_of_getElem? hb))
    · exact ih (i0 + 1) h4 c (by omega) (by simp at h2; omega)

/-- **The lines clause for every class of a local table, from the lines clause of the table `B`'s records and the advice.** -/
theorem linesLoc_of_adv (t5 : List T5Rec) (tg : ℕ → ℤ) (S nT : ℕ) (bls : List (ℕ × List (ℕ × ℕ)))
    (adv : List (ℕ × ℕ × List ℤ)) (hl : adv.length = nT) (h : eqAll tg S (assoc bls) 0 adv = true)
    (hs : ∀ e ∈ bls, ∀ p ∈ e.2, LinesCl t5 (t4OfRec p.1)) :
    ∀ cl ∈ (List.range nT).map (t4At tg S), LinesCl t5 cl := by
  intro cl hcl
  obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hcl
  refine eqAll_sound t5 tg S (assoc bls) ?_ adv 0 h c (Nat.zero_le _) (by rw [List.mem_range] at hc; omega)
  intro j p hp
  obtain ⟨e, he, hpe⟩ := assoc_mem hp
  exact hs e he p hpe

#print axioms linesCl_transfer
#print axioms eqChk_sound
#print axioms linesLoc_of_adv

end L5Reg
end LRSpectrumFull

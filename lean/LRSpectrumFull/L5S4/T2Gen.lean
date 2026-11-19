/-
# L5S4.T2Gen : `StreamHyp'.t2` for a depth-1 node with the representative set restricted to the class LEADERS (stage S4R)

`GT2.t2_nK'` returns `rep ∈ R2K` where `R2K` (CheckChildRec) holds EVERY stored survivor of the node (730 at node #4), so the
`t3` clause over `R2K` would have to be proved for 30,649 depth-2 nodes in total.  The design needs `t3` only for the 1,965 class
leaders.  `t2_lead` has the same shape but returns the representative from `R2Lead n L lead`: the nodes of the records of `L`
at the positions in `lead`.  The class map `d2Ok` of every record points at `L.getD (cRep r)`, so `lead := (L.map cRep).dedup`
(a decidable list, no new data) works, and `hlead` is `List.mem_dedup`.

* `R2Lead`, `t2_lead` : the generic statement, for ANY node `n`, packed data `P` and flat record check (`recN`).
* `t2_of_link` : the link used by the aggregation.  Only `rep.rows` enters `Chain2Rel`; if every leader record `L[j]` has a node
  `m ∈ R2` (the block of the rollout, `N<rep>.nK`) with `m.rows = setRow n.rows 1 (cY L[j])`, then `rep ∈ R2`.
* `hrad1_of` : the radius hypothesis of a depth-1 node `nodeOfRaw r hr` from the rational data (replaces the node-by-node proof
  `hrad_nK`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GBr2
import LRSpectrumFull.L5S4.GFlat

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

set_option maxRecDepth 100000

theorem flatMap_unpack' (P : List (ℤ × List ℕ)) :
    (P.map fun g => (g.1, g.2.map unpackRec)).flatMap Prod.snd = (P.flatMap Prod.snd).map unpackRec := by
  induction P with
  | nil => rfl
  | cons a P ih => simp [List.flatMap_cons, List.map_append, ih]

/-- the leader nodes: the nodes of the records of `L` at the positions `lead` -/
def R2Lead (n : NodeW 1 4) (L : List (List ℤ)) (lead : List ℕ) : Set (NodeW 2 3) :=
  {m | ∃ j ∈ lead, ∃ h : RecFacts n (L.getD j []), m = nodeOf2 n (L.getD j []) h}

/-- **`StreamHyp'.t2` with leaders only, list form.**  `L` is the list of stored records. -/
theorem t2_lead_aux (n : NodeW 1 4) (L : List (List ℤ)) (hall : ∀ r ∈ L, recOkB n L r = true)
    (hcomp : ∀ y : V5, ChildPass n y → ∃ r ∈ L, recT r = tvec n.b y)
    (lead : List ℕ) (hlead : ∀ r ∈ L, cRep r ∈ lead) :
    ∀ y : V5, ChildPass n y → ∃ (y' : V5) (n2 : NodeW 2 3),
      (∀ i, dot (n.b i) y' = dot (n.b i) y) ∧ n2.rows = setRow n.rows 1 y' ∧
      ∃ rep ∈ R2Lead n L lead, ∃ (g : SP) (U U' : ℕ → ℕ → ℤ), Chain2Rel g n2.rows rep.rows U U' := by
  intro y hy
  obtain ⟨r, hrL, hrt⟩ := hcomp y hy
  obtain ⟨hf, hlen, g', U, U', hch⟩ := recOk_sound n L r (hall r hrL)
  have hrp : L.getD (cRep r) [] ∈ L := by
    have : L.getD (cRep r) [] = L[cRep r] := by simp [List.getD_eq_getElem?_getD, hlen]
    rw [this]; exact List.getElem_mem hlen
  obtain ⟨hfp, -, -⟩ := recOk_sound n L _ (hall _ hrp)
  refine ⟨cY r, nodeOf2 n r hf, fun i => ?_, rfl, nodeOf2 n _ hfp, ⟨cRep r, hlead r hrL, hfp, rfl⟩, g', U, U', hch⟩
  have h1 := hf.1 i
  have h2 := congrFun hrt i
  rw [h1]; simpa [tvec] using h2

/-- **`StreamHyp'.t2` with leaders only, packed form.**  `hcomp` : every child has a stored record (list completeness,
flat scan); `hrec` : every stored record passes the packed check (facts + class map to `L.getD (cRep r)`); `hlead` : every
class map points at a position of `lead`. -/
theorem t2_lead (n : NodeW 1 4) (bn bd : ℤ) (P : List (ℤ × List ℕ))
    (hcomp : ∀ y : V5, ChildPass n y →
      ∃ g ∈ (P.map fun g => (g.1, g.2.map unpackRec)), ∃ r ∈ g.2, recT r = tvec n.b y)
    (hrec : ∀ N ∈ P.flatMap Prod.snd, recN (FC.ofCtx (ctxOf n bn bd)) (P.flatMap Prod.snd) N = true)
    (lead : List ℕ) (hlead : ∀ N ∈ P.flatMap Prod.snd, cRep (unpackRec N) ∈ lead) :
    ∀ y : V5, ChildPass n y → ∃ (y' : V5) (n2 : NodeW 2 3),
      (∀ i, dot (n.b i) y' = dot (n.b i) y) ∧ n2.rows = setRow n.rows 1 y' ∧
      ∃ rep ∈ R2Lead n ((P.flatMap Prod.snd).map unpackRec) lead, ∃ (g : SP) (U U' : ℕ → ℕ → ℤ),
        Chain2Rel g n2.rows rep.rows U U' := by
  refine t2_lead_aux n ((P.flatMap Prod.snd).map unpackRec) ?_ ?_ lead ?_
  · intro r hr
    obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hr
    exact recOkN_sound n bn bd (P.flatMap Prod.snd) N (hrec N hN)
  · intro y hy
    obtain ⟨g, hg, r, hr, hrt⟩ := hcomp y hy
    refine ⟨r, ?_, hrt⟩
    rw [← flatMap_unpack']
    exact List.mem_flatMap.2 ⟨g, hg, hr⟩
  · intro r hr
    obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hr
    exact hlead N hN

/-- **The link to a block.**  `R2` is any set of depth-2 nodes (the block of the rollout).  Only the rows of the representative
enter `Chain2Rel`, so it suffices that every leader record has a node of `R2` with the same rows. -/
theorem t2_of_link (n : NodeW 1 4) (bn bd : ℤ) (P : List (ℤ × List ℕ))
    (hcomp : ∀ y : V5, ChildPass n y →
      ∃ g ∈ (P.map fun g => (g.1, g.2.map unpackRec)), ∃ r ∈ g.2, recT r = tvec n.b y)
    (hrec : ∀ N ∈ P.flatMap Prod.snd, recN (FC.ofCtx (ctxOf n bn bd)) (P.flatMap Prod.snd) N = true)
    (lead : List ℕ) (hlead : ∀ N ∈ P.flatMap Prod.snd, cRep (unpackRec N) ∈ lead)
    (R2 : Set (NodeW 2 3))
    (hlink : ∀ j ∈ lead, ∃ m ∈ R2,
      m.rows = setRow n.rows 1 (cY (((P.flatMap Prod.snd).map unpackRec).getD j []))) :
    ∀ y : V5, ChildPass n y → ∃ (y' : V5) (n2 : NodeW 2 3),
      (∀ i, dot (n.b i) y' = dot (n.b i) y) ∧ n2.rows = setRow n.rows 1 y' ∧
      ∃ rep ∈ R2, ∃ (g : SP) (U U' : ℕ → ℕ → ℤ), Chain2Rel g n2.rows rep.rows U U' := by
  intro y hy
  obtain ⟨y', n2, h1, h2, rep, ⟨j, hj, hfj, hrepe⟩, g, U, U', hch⟩ := t2_lead n bn bd P hcomp hrec lead hlead y hy
  obtain ⟨m, hm, hmr⟩ := hlink j hj
  have hrows : rep.rows = m.rows := by
    rw [hmr, hrepe]; exact nodeOf2_rows n _ hfj
  exact ⟨y', n2, h1, h2, m, hm, g, U, U', by rw [← hrows]; exact hch⟩

/-! ## Radius of a depth-1 node from its rational data -/

theorem hrad1_of (r : D1Raw) (hr : r.ok) (q : ℚ)
    (hq : (q = 37 / 9 / (4 * (1 / 2 - 1 / 5 : ℚ) ^ 2 - 1 / (dot r.h r.h : ℚ)) ∧
            0 < 4 * (1 / 2 - 1 / 5 : ℚ) ^ 2 - 1 / (dot r.h r.h : ℚ) ∧
            (0 < 4 * ((wMin r.x r.w : ℚ) / r.w - 1 / 5) ^ 2 →
              q ≤ 37 / 9 / (4 * ((wMin r.x r.w : ℚ) / r.w - 1 / 5) ^ 2))) ∨
         (q = 37 / 9 / (4 * ((wMin r.x r.w : ℚ) / r.w - 1 / 5) ^ 2) ∧
            0 < 4 * ((wMin r.x r.w : ℚ) / r.w - 1 / 5) ^ 2 ∧
            (0 < 4 * (1 / 2 - 1 / 5 : ℚ) ^ 2 - 1 / (dot r.h r.h : ℚ) →
              q ≤ 37 / 9 / (4 * (1 / 2 - 1 / 5 : ℚ) ^ 2 - 1 / (dot r.h r.h : ℚ))))) :
    radFrac (Cq (1 + 1)) (nodeOfRaw r hr).wit (nodeOfRaw r hr).rows 1 (nodeOfRaw r hr).rk = q := by
  have hw0 : cOf ((nodeOfRaw r hr).wit 0) = 1 / 2 := by simp [nodeOfRaw, d1Wit, cOf, wMin]
  have hw1 : cOf ((nodeOfRaw r hr).wit 1) = (wMin r.x r.w : ℚ) / r.w := by
    simp [nodeOfRaw, d1Wit, cOf]
  have hrow0 : hN (nodeOfRaw r hr).rows 0 = r.h := nodeOfRaw_row0 r hr
  have hS0 : SArr (nodeOfRaw r hr).rows 1 0 = 1 / (dot r.h r.h : ℚ) := by
    simp [SArr, Gm_zero, Gm_one, hrow0]
  have hS1 : SArr (nodeOfRaw r hr).rows 1 1 = 0 := by simp [SArr]
  have hC : Cq (1 + 1) = 37 / 9 := by norm_num [Cq, Finset.sum_range_succ]
  rw [hC]
  have hk : ∀ k, k ∈ radSet (nodeOfRaw r hr).wit (nodeOfRaw r hr).rows 1 ↔
      (k = 0 ∧ 0 < 4 * (1 / 2 - 1 / 5 : ℚ) ^ 2 - 1 / (dot r.h r.h : ℚ)) ∨
      (k = 1 ∧ 0 < 4 * ((wMin r.x r.w : ℚ) / r.w - 1 / 5) ^ 2) := by
    intro k
    simp only [radSet, Finset.mem_filter, Finset.mem_range]
    constructor
    · rintro ⟨hk2, hpos⟩
      have : k = 0 ∨ k = 1 := by omega
      rcases this with rfl | rfl
      · left; refine ⟨rfl, ?_⟩; rw [hw0, hS0] at hpos; exact hpos
      · right; refine ⟨rfl, ?_⟩; rw [hw1, hS1] at hpos; simpa using hpos
    · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩)
      · refine ⟨by norm_num, ?_⟩; rw [hw0, hS0]; exact h
      · refine ⟨by norm_num, ?_⟩; rw [hw1, hS1]; simpa using h
  have hval0 : 37 / 9 / (4 * (cOf ((nodeOfRaw r hr).wit 0) - 1 / 5) ^ 2 - SArr (nodeOfRaw r hr).rows 1 0)
      = 37 / 9 / (4 * (1 / 2 - 1 / 5 : ℚ) ^ 2 - 1 / (dot r.h r.h : ℚ)) := by rw [hw0, hS0]
  have hval1 : 37 / 9 / (4 * (cOf ((nodeOfRaw r hr).wit 1) - 1 / 5) ^ 2 - SArr (nodeOfRaw r hr).rows 1 1)
      = 37 / 9 / (4 * ((wMin r.x r.w : ℚ) / r.w - 1 / 5) ^ 2) := by rw [hw1, hS1]; simp
  rcases hq with ⟨e, hp, hle⟩ | ⟨e, hp, hle⟩
  · apply radFrac_eq_of
    · exact ⟨0, (hk 0).2 (Or.inl ⟨rfl, hp⟩), by rw [hval0]; exact e.symm⟩
    · intro k hkk
      rcases (hk k).1 hkk with ⟨rfl, _⟩ | ⟨rfl, h1⟩
      · rw [hval0]; exact e.le
      · rw [hval1]; exact hle h1
  · apply radFrac_eq_of
    · exact ⟨1, (hk 1).2 (Or.inr ⟨rfl, hp⟩), by rw [hval1]; exact e.symm⟩
    · intro k hkk
      rcases (hk k).1 hkk with ⟨rfl, h0⟩ | ⟨rfl, _⟩
      · rw [hval0]; exact hle h0
      · rw [hval1]; exact e.le

end L5S4
end LRSpectrumFull

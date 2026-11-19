/-
# L5S4.Records : certificate records, class transport, and the statement of `tree_complete`

Case-tree certificate, part 3.  Mirrors `lean5_wp0a/src/cert.rs` (T1, T2, T2c, T3, T4, T5).

1. Record types of the three levels (depth-1 reps, depth-2 chain classes, leaf records, leaf classes with integer
   `|v|²` ranges, residual tuples) and the `Certificate`.  Integers are `ℤ`, the signed permutation is `SP`
   (Rust `G`), the matrices `U, U'` of `leq_ok` are `ℕ → ℕ → ℤ` (restricted to the first `d` rows).
2. The relations the checker verifies, as Props: `LeqOkN` (= Rust `leq_ok`: `t = U b`, `b = U' t`), `Chain1Rel`,
   `Chain2Rel` (first row preserved up to sign + lattice equality), `Leaf3Rel`.
3. PROVED class transport (E10, completeness of the symmetry quotient):
   `chain2_rep_flag` : for an accepted flag `F` of a near-tight `v` and a record `Chain2Rel g F.h rep U U'` there is an
   ACCEPTED flag of `g v` whose first two rows are exactly the stored representative `rep`;
   `chain1_rep_flag` likewise for depth 1; `leaf_orth` : `rep ⟂ g v` for a leaf class map;
   `depth1_cover` : every primitive `h` with `2 ≤ |h|² ≤ 18` is mapped by some `g` to a sorted nonnegative vector with
   entries `≤ 4` (the 26 depth-1 reps are among them; the Rust enumerates exactly these).
4. `TreeHyp` : the statements the S4 checkers must establish (named hypotheses, none proved here) and `tree_complete`,
   the final tree theorem, proved from `TreeHyp` and the PROVED lemmas above.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.ChainRep
import Mathlib.Data.Fin.Tuple.Sort

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. Record types -/

/-- Depth-1 representative: row `h`, witness `x / w` for `M(L_1)` (`T1`). -/
structure T1Rec where
  h : V5
  x : V5
  w : ℤ

/-- Depth-2 survivor record (`T2`): witness, class id, map `g` to the class representative, `U, U'` (2×2). -/
structure T2Rec where
  x : V5
  w : ℤ
  cls : ℕ
  g : SP
  U : ℕ → ℕ → ℤ
  U' : ℕ → ℕ → ℤ

/-- Depth-2 class representative (`T2c`), with the node data the checker recomputes by `child`:
rows `l`, a basis `b` of `L^⊥ ∩ ℤ^5` with right inverse `r` (E6: the checker verifies the identities). -/
structure T2cRec where
  hi : ℕ
  t : Fin 4 → ℤ
  g : SP
  l : Fin 4 → V5

/-- Leaf flag (`T3`): empty window, critical leaf (identification with `V_ck`), or class map (3×3). -/
inductive LeafFlag
  | empty
  | crit (ck : Fin 2) (g : SP) (U U' : ℕ → ℕ → ℤ)
  | mapped (cls : ℕ) (g : SP) (U U' : ℕ → ℕ → ℤ)

structure T3Rec where
  x : V5
  w : ℤ
  flag : LeafFlag

/-- Leaf class (`T4`): `g` canonical map, rows `l` of `L_3`, basis `k` of `K_3 = L_3^⊥`, certificate `Q` (2×5), `P` (5×3),
merged integer ranges of `|v|²` (inclusive). -/
structure T4Rec where
  g : SP
  l : Fin 3 → V5
  k : Fin 2 → V5
  q : Fin 2 → Fin 5 → ℤ
  p : Fin 3 → V5
  ranges : List (ℤ × ℤ)

/-- Residual tuple (`T5`): a line with no witness in the 548 times (extra time `a/q`, value `mln/mld`). -/
structure T5Rec where
  v : V5
  kind : ℕ
  a : ℤ
  q : ℤ
  mln : ℤ
  mld : ℤ

/-- The certificate: streams in the order of the enumeration loops (the checker consumes them exactly). -/
structure Certificate where
  t1 : List T1Rec
  t2 : List (List T2Rec)
  t2c : List T2cRec
  t3 : List (List T3Rec)
  t4 : List T4Rec
  t5 : List T5Rec

/-! ## 2. The relations the checker verifies -/

/-- Rust `leq_ok(t, b, U, U')` on the first `d` rows: `t_i = ∑ U_ik b_k` and `b_i = ∑ U'_ik t_k`. -/
def LeqOkN (d : ℕ) (t b : Fin 4 → V5) (U U' : ℕ → ℕ → ℤ) : Prop :=
  (∀ i < d, ∀ c, hN t i c = ∑ k ∈ range d, U i k * hN b k c) ∧
  (∀ i < d, ∀ c, hN b i c = ∑ k ∈ range d, U' i k * hN t k c)

/-- Depth 1: the first row is mapped to the stored one up to sign. -/
def Chain1Rel (g : SP) (rows rep : Fin 4 → V5) : Prop :=
  g.act (hN rows 0) = hN rep 0 ∨ g.act (hN rows 0) = fun a => - hN rep 0 a

/-- Depth 2 (`T2` check): first row preserved up to sign and `L_2` equal as a lattice. -/
def Chain2Rel (g : SP) (rows rep : Fin 4 → V5) (U U' : ℕ → ℕ → ℤ) : Prop :=
  Chain1Rel g rows rep ∧ LeqOkN 2 (fun i => g.act (rows i)) rep U U'

/-- Leaf (`T3` check, `flag = mapped`): `L_3` equal as a lattice (no chain information). -/
def Leaf3Rel (g : SP) (rows rep : Fin 4 → V5) (U U' : ℕ → ℕ → ℤ) : Prop :=
  LeqOkN 3 (fun i => g.act (rows i)) rep U U'

/-- Non-vacuity: the identity map is a class map. -/
def SP.one : SP := ⟨Equiv.refl _, fun _ => 1, fun _ => Or.inl rfl⟩

theorem act_one (x : V5) : SP.one.act x = x := by
  funext i; simp [SP.act, SP.one]

def idN : ℕ → ℕ → ℤ := fun i k => if i = k then 1 else 0

theorem chain2_refl (rows : Fin 4 → V5) : Chain2Rel SP.one rows rows idN idN := by
  refine ⟨Or.inl (by rw [act_one]), ?_, ?_⟩ <;>
  · intro i hi c
    simp only [act_one, idN]
    simp [Finset.sum_ite_eq, hi]

/-! ## 3. Class transport (E10: completeness of the symmetry quotient) -/

/-- Depth 1.  An accepted flag of a near-tight `v` and a record `Chain1Rel g F.h rep` give an accepted flag of
`g v` whose first row is exactly `rep 0`. -/
theorem chain1_rep_flag {v : V5} (hv : Primitive v) (hnz : ∀ i, v i ≠ 0) (hlt : ML v < 1 / 5)
    (F : FlagData v) (hacc : Accepted F) (g : SP) (rep : Fin 4 → V5) (hrel : Chain1Rel g F.h rep) :
    ∃ F' : FlagData (g.act v), Accepted F' ∧ F'.h 0 = rep 0 := by
  have hP : PrefixEq (F.act g) rep 1 := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst hi0
    have h0 : hN (F.act g).h 0 = g.act (hN F.h 0) := by
      funext a; simp [hN, L5S3.FlagData.act]
    rcases hrel with e | e
    · refine ⟨⟨fun _ => 1, fun a => ?_⟩, ⟨fun _ => 1, fun a => ?_⟩⟩ <;>
      · have := congrFun e a
        (simp [h0]) <;> linarith [this]
    · refine ⟨⟨fun _ => -1, fun a => ?_⟩, ⟨fun _ => -1, fun a => ?_⟩⟩ <;>
      · have := congrFun e a
        (simp [h0]) <;> linarith [this]
  obtain ⟨F', hacc', _, hrows⟩ := accepted_act_prefix hv hnz hlt F hacc.greedy g rep 1 (by omega) hP
  exact ⟨F', hacc', hrows 0 (by simp)⟩

/-- Depth 2 (**the completeness lemma of the symmetry quotient**).  For an accepted flag `F` of a near-tight `v` and a
record `Chain2Rel g F.h rep U U'`, there is an ACCEPTED flag of `g v` whose first two rows are exactly the stored
representative rows `rep 0`, `rep 1`.  Hence every filter of the generator, read on the representative node, holds for
the image of every member of its class. -/
theorem chain2_rep_flag {v : V5} (hv : Primitive v) (hnz : ∀ i, v i ≠ 0) (hlt : ML v < 1 / 5)
    (F : FlagData v) (hacc : Accepted F) (g : SP) (rep : Fin 4 → V5) (U U' : ℕ → ℕ → ℤ)
    (hrel : Chain2Rel g F.h rep U U') :
    ∃ F' : FlagData (g.act v), Accepted F' ∧ F'.h 0 = rep 0 ∧ F'.h 1 = rep 1 := by
  obtain ⟨h1, hu, hu'⟩ := hrel
  have h0 : hN (F.act g).h 0 = g.act (hN F.h 0) := by
    funext a; simp [hN, L5S3.FlagData.act]
  have hP : PrefixEq (F.act g) rep 2 := by
    intro i hi
    have hi2 : i = 0 ∨ i = 1 := by omega
    rcases hi2 with rfl | rfl
    · rcases h1 with e | e
      · refine ⟨⟨fun _ => 1, fun a => ?_⟩, ⟨fun _ => 1, fun a => ?_⟩⟩ <;>
        · have := congrFun e a
          (simp [h0]) <;> linarith [this]
      · refine ⟨⟨fun _ => -1, fun a => ?_⟩, ⟨fun _ => -1, fun a => ?_⟩⟩ <;>
        · have := congrFun e a
          (simp [h0]) <;> linarith [this]
    · refine ⟨⟨fun k => U' 1 k, fun a => ?_⟩, ⟨fun k => U 1 k, fun a => ?_⟩⟩
      · exact hu' 1 (by omega) a
      · exact hu 1 (by omega) a
  obtain ⟨F', hacc', _, hrows⟩ := accepted_act_prefix hv hnz hlt F hacc.greedy g rep 2 (by omega) hP
  exact ⟨F', hacc', hrows 0 (by simp), hrows 1 (by simp)⟩

/-- Leaf: a leaf class map sends `v` into the orthogonal complement of the stored lattice `rep` (`K_3` of the class). -/
theorem leaf_orth {v : V5} (F : FlagData v) (g : SP) (rep : Fin 4 → V5) (U U' : ℕ → ℕ → ℤ)
    (hrel : Leaf3Rel g F.h rep U U') (i : ℕ) (hi : i < 3) : dot (hN rep i) (g.act v) = 0 := by
  have h1 := hrel.2 i hi
  have e : dot (hN rep i) (g.act v) = ∑ k ∈ range 3, U' i k * dot (hN (fun m => g.act (F.h m)) k) (g.act v) := by
    unfold dot
    calc ∑ a, hN rep i a * g.act v a = ∑ a, (∑ k ∈ range 3, U' i k * hN (fun m => g.act (F.h m)) k a) * g.act v a := by
          refine Finset.sum_congr rfl (fun a _ => ?_)
          rw [h1 a]
      _ = ∑ k ∈ range 3, U' i k * ∑ a, hN (fun m => g.act (F.h m)) k a * g.act v a := by
          simp only [Finset.sum_mul]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl (fun k _ => ?_)
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun a _ => by ring)
  rw [e]
  apply Finset.sum_eq_zero
  intro k hk
  have hk3 : k < 3 := mem_range.1 hk
  have hk4 : k < 4 := by omega
  have : dot (hN (fun m => g.act (F.h m)) k) (g.act v) = 0 := by
    have hh : hN (fun m => g.act (F.h m)) k = g.act (F.h ⟨k, hk4⟩) := by
      simp [hN, hk4]
    rw [hh, dot_act]
    exact F.hv ⟨k, hk4⟩
  rw [this, mul_zero]

/-! ## 3b. Depth-1 cover by sorting -/

theorem exists_sort_abs (h : V5) :
    ∃ g : SP, ∀ i j : Fin 5, i ≤ j → 0 ≤ g.act h i ∧ g.act h i ≤ g.act h j := by
  let a : Fin 5 → ℤ := fun i => |h i|
  let σ := Tuple.sort a
  have hm : Monotone (a ∘ σ) := Tuple.monotone_sort a
  let ε : Fin 5 → ℤ := fun i => if 0 ≤ h (σ i) then 1 else -1
  have hε : ∀ i, ε i = 1 ∨ ε i = -1 := fun i => by
    by_cases hh : 0 ≤ h (σ i) <;> simp [ε, hh]
  have key : ∀ i, (SP.act ⟨σ, ε, hε⟩ h) i = |h (σ i)| := by
    intro i
    by_cases hh : 0 ≤ h (σ i)
    · simp [SP.act, ε, hh, abs_of_nonneg hh]
    · simp [SP.act, ε, hh, abs_of_neg (not_le.mp hh)]
  refine ⟨⟨σ, ε, hε⟩, fun i j hij => ?_⟩
  rw [key, key]
  exact ⟨abs_nonneg _, hm hij⟩

/-- The depth-1 reps are sorted nonnegative vectors with entries `≤ 4` and `2 ≤ |h|² ≤ 18`. -/
def T1Ok (h : V5) : Prop :=
  (∀ i j : Fin 5, i ≤ j → 0 ≤ h i ∧ h i ≤ h j) ∧ (∀ i, h i ≤ 4) ∧ Primitive h ∧ 2 ≤ dot h h ∧ dot h h ≤ 18

theorem sq_le_dot (h : V5) (i : Fin 5) : h i * h i ≤ dot h h := by
  unfold dot
  exact Finset.single_le_sum (f := fun k => h k * h k) (fun k _ => mul_self_nonneg _) (Finset.mem_univ i)

theorem depth1_cover (h : V5) (hp : Primitive h) (h2 : 2 ≤ dot h h) (h18 : dot h h ≤ 18) :
    ∃ g : SP, T1Ok (g.act h) := by
  obtain ⟨g, hg⟩ := exists_sort_abs h
  refine ⟨g, hg, fun i => ?_, primitive_act hp g, by rw [dot_act]; exact h2, by rw [dot_act]; exact h18⟩
  have h1 := sq_le_dot (g.act h) i
  rw [dot_act] at h1
  have h0 := (hg i i le_rfl).1
  nlinarith

/-! ## 4. The statements of the tree theorem -/

/-- Near-tight: primitive, all entries nonzero, `ML < 1/5`. -/
def NearTight (v : V5) : Prop := Primitive v ∧ (∀ i, v i ≠ 0) ∧ ML v < 1 / 5

/-- `rows` are the first `j` rows of an accepted flag of the near-tight `v`. -/
def RealizableV (j : ℕ) (rows : Fin 4 → V5) (v : V5) : Prop :=
  NearTight v ∧ ∃ F : FlagData v, Accepted F ∧ ∀ i : Fin 4, i.val < j → F.h i = rows i

/-- Realizability is closed under the symmetry group (the quotient is sound). -/
theorem realizable_act {j : ℕ} {rows : Fin 4 → V5} {v : V5} (h : RealizableV j rows v) (g : SP) :
    RealizableV j (fun i => g.act (rows i)) (g.act v) := by
  obtain ⟨⟨hv, hnz, hlt⟩, F, hacc, hrows⟩ := h
  refine ⟨⟨primitive_act hv g, nz_act hnz g, by rw [ML_act]; exact hlt⟩, F.act g, ?_, ?_⟩
  · exact accepted_act hv hnz hlt F hacc.greedy g
  · intro i hi
    simp only [L5S3.FlagData.act, hrows i hi]

/-- Critical torus of kind `k`: `u = A (V_k, 0) + B e_5` with `V_0 = (1,2,3,4)`, `V_1 = (1,3,4,7)`. -/
def CritTorus (k : Fin 2) (u : V5) : Prop :=
  ∃ A B : ℤ, (∀ i : Fin 4, u i.castSucc = A * (if k = 0 then ![1, 2, 3, 4] else ![1, 3, 4, 7]) i) ∧ u 4 = B

/-- A leaf class table entry `cl` contains `u` in its lattice complement and the integer `|u|²` in one of its ranges. -/
def InClass (cl : T4Rec) (u : V5) : Prop :=
  (∀ i : Fin 3, dot (cl.l i) u = 0) ∧ ∃ r ∈ cl.ranges, r.1 ≤ dot u u ∧ dot u u ≤ r.2

/-- The statements the S4 checkers must establish (NAMED HYPOTHESES; nothing here is proved).  Each field is the
mathematical content of one verified stream of the certificate:
* `leaf`  : T1 + T2 + T2c + T3 completeness (for every realizable chain of three rows: a critical identification or a
  class map into a stored class, with the window range containing `|v|²`);
* `lines` : T4 + line loops + T5: every primitive `u` of a stored class with distinct nonzero absolute entries whose
  `|u|²` lies in a range of the class satisfies `1/5 ≤ ML u` (witnessed) or equals a residual tuple. -/
structure TreeHyp (C : Certificate) : Prop where
  leaf : ∀ (v : V5) (rows : Fin 4 → V5), RealizableV 3 rows v →
    (∃ (k : Fin 2) (g : SP), CritTorus k (g.act v)) ∨
    (∃ cl ∈ C.t4, ∃ (g : SP) (U U' : ℕ → ℕ → ℤ), Leaf3Rel g rows (fun i => if h : i.val < 3 then cl.l ⟨i.val, h⟩ else fun _ => 0) U U' ∧
      ∃ r ∈ cl.ranges, r.1 ≤ dot v v ∧ dot v v ≤ r.2)
  lines : ∀ cl ∈ C.t4, ∀ u : V5, Primitive u → (∀ i, u i ≠ 0) → (∀ i j, i ≠ j → |u i| ≠ |u j|) →
    InClass cl u → (∃ r ∈ C.t5, ∃ g : SP, g.act u = r.v) ∨ 1 / 5 ≤ ML u

/-- **The tree theorem.**  Every near-tight `v` with pairwise distinct absolute entries lies, up to a signed
permutation, on a critical torus, or is a stored residual tuple.  Proved from `TreeHyp` and the PROVED class lemmas. -/
theorem tree_complete {C : Certificate} (H : TreeHyp C) (v : V5) (hnt : NearTight v)
    (hdist : ∀ i j, i ≠ j → |v i| ≠ |v j|) :
    (∃ (k : Fin 2) (g : SP), CritTorus k (g.act v)) ∨ (∃ r ∈ C.t5, ∃ g : SP, g.act v = r.v) := by
  obtain ⟨hv, hnz, hlt⟩ := hnt
  obtain ⟨F, hacc⟩ : ∃ F : FlagData v, Accepted F := exists_flag_accepted v hv hnz hlt
  have hr : RealizableV 3 F.h v := ⟨⟨hv, hnz, hlt⟩, F, hacc, fun i _ => rfl⟩
  rcases H.leaf v F.h hr with hc | ⟨cl, hcl, g, U, U', hrel, rg, hrg, hlo, hhi⟩
  · exact Or.inl hc
  · -- the image `u = g v` lies in the class complement and its norm is in a range
    have hu : InClass cl (g.act v) := by
      refine ⟨fun i => ?_, rg, hrg, ?_, ?_⟩
      · have := leaf_orth F g _ U U' hrel i.val i.2
        have hi4 : i.val < 4 := by omega
        simpa [hN, i.2, hi4] using this
      · rw [dot_act]; exact hlo
      · rw [dot_act]; exact hhi
    have hd : ∀ i j, i ≠ j → |g.act v i| ≠ |g.act v j| := by
      intro i j hij
      simp only [SP.act, abs_mul]
      rcases g.hε i with a | a <;> rcases g.hε j with b | b <;> simp [a, b] <;>
        exact hdist _ _ (fun h => hij (g.σ.injective h))
    rcases H.lines cl hcl (g.act v) (primitive_act hv g) (nz_act hnz g) hd hu with ⟨r, hr, g2, hg2⟩ | hge
    · refine Or.inr ⟨r, hr, g2.mul g, ?_⟩
      rw [act_mul]; exact hg2
    · exact absurd (by rw [ML_act] at hge; exact hge) (not_le.2 hlt)

end L5S4
end LRSpectrumFull

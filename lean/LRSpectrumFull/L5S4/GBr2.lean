/-
# L5S4.GBr2 : class-map bridge and `recN -> recOkB` (stage S4 block 8)

`d2Ok_of_G`    : `recClassG f g z = true` gives `d2Ok` of the class record `[h, cY r] -> [h, y']` with `y' i = z (4 + i)`.
`recOkN_sound` : the packed-Nat flat check `recN` accepting a record implies the original relation `recOkB` on the unpacked
                 records (`unpackRec`), for every node `n` and every list of packed records.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GBr

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

set_option maxRecDepth 100000

theorem hN_rowsL0 (h y : V5) : hN (rowsL [h, y]) 0 = h := by simp [hN, rowsL]
theorem hN_rowsL1 (h y : V5) : hN (rowsL [h, y]) 1 = y := by simp [hN, rowsL]

theorem leq_core (G : SP) (h y yp : V5) (U U' : ℕ → ℕ → ℤ)
    (a : ∀ c, G.act h c = U 0 0 * h c + U 0 1 * yp c)
    (cc : ∀ c, G.act y c = U 1 0 * h c + U 1 1 * yp c)
    (v : ∀ c, h c = U' 0 0 * G.act h c + U' 0 1 * G.act y c)
    (w : ∀ c, yp c = U' 1 0 * G.act h c + U' 1 1 * G.act y c) :
    LeqOkN 2 (fun i => G.act (rowsL [h, y] i)) (rowsL [h, yp]) U U' := by
  constructor
  · intro i hi c
    interval_cases i
    · simpa [hN, rowsL, Finset.sum_range_succ] using a c
    · simpa [hN, rowsL, Finset.sum_range_succ] using cc c
  · intro i hi c
    interval_cases i
    · simpa [hN, rowsL, Finset.sum_range_succ] using v c
    · simpa [hN, rowsL, Finset.sum_range_succ] using w c

theorem chain1_core (G : SP) (h y yp : V5)
    (hA : (∀ c, G.act h c = h c) ∨ (∀ c, G.act h c = -h c)) : Chain1Rel G (rowsL [h, y]) (rowsL [h, yp]) := by
  unfold Chain1Rel
  rw [hN_rowsL0, hN_rowsL0]
  rcases hA with hh | hh
  · exact Or.inl (funext hh)
  · exact Or.inr (funext fun c => hh c)

theorem inj_of_ne (s : Fin 5 → ℕ) (n01 : s 0 ≠ s 1) (n02 : s 0 ≠ s 2) (n03 : s 0 ≠ s 3) (n04 : s 0 ≠ s 4)
    (n12 : s 1 ≠ s 2) (n13 : s 1 ≠ s 3) (n14 : s 1 ≠ s 4) (n23 : s 2 ≠ s 3) (n24 : s 2 ≠ s 4) (n34 : s 3 ≠ s 4) :
    Function.Injective s := by
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    first | rfl | exact (n01 hij).elim | exact (n01 hij.symm).elim | exact (n02 hij).elim | exact (n02 hij.symm).elim |
      exact (n03 hij).elim | exact (n03 hij.symm).elim | exact (n04 hij).elim | exact (n04 hij.symm).elim |
      exact (n12 hij).elim | exact (n12 hij.symm).elim | exact (n13 hij).elim | exact (n13 hij.symm).elim |
      exact (n14 hij).elim | exact (n14 hij.symm).elim | exact (n23 hij).elim | exact (n23 hij.symm).elim |
      exact (n24 hij).elim | exact (n24 hij.symm).elim | exact (n34 hij).elim | exact (n34 hij.symm).elim

theorem gp_ok (r : List ℤ) (g : ℕ → ℤ) (hr' : ∀ k, k < 64 → r.getD k 0 = g k)
    (hr2 : ∀ k, k < 64 → r[k]?.getD 0 = g k)
    (n01 : ¬ (g 46).toNat % 5 = (g 47).toNat % 5) (n02 : ¬ (g 46).toNat % 5 = (g 48).toNat % 5)
    (n03 : ¬ (g 46).toNat % 5 = (g 49).toNat % 5) (n04 : ¬ (g 46).toNat % 5 = (g 50).toNat % 5)
    (n12 : ¬ (g 47).toNat % 5 = (g 48).toNat % 5) (n13 : ¬ (g 47).toNat % 5 = (g 49).toNat % 5)
    (n14 : ¬ (g 47).toNat % 5 = (g 50).toNat % 5) (n23 : ¬ (g 48).toNat % 5 = (g 49).toNat % 5)
    (n24 : ¬ (g 48).toNat % 5 = (g 50).toNat % 5) (n34 : ¬ (g 49).toNat % 5 = (g 50).toNat % 5)
    (e0 : g 51 = 1 ∨ g 51 = -1) (e1 : g 52 = 1 ∨ g 52 = -1) (e2 : g 53 = 1 ∨ g 53 = -1)
    (e3 : g 54 = 1 ∨ g 54 = -1) (e4 : g 55 = 1 ∨ g 55 = -1) : gOk (gpOf r) := by
  refine ⟨?_, ?_⟩
  · have hs : Function.Injective (fun i => ((gpOf r).1 i).val) :=
      inj_of_ne _ (by simpa [gpOf, hr', hr2] using n01) (by simpa [gpOf, hr', hr2] using n02)
        (by simpa [gpOf, hr', hr2] using n03) (by simpa [gpOf, hr', hr2] using n04)
        (by simpa [gpOf, hr', hr2] using n12) (by simpa [gpOf, hr', hr2] using n13)
        (by simpa [gpOf, hr', hr2] using n14) (by simpa [gpOf, hr', hr2] using n23)
        (by simpa [gpOf, hr', hr2] using n24) (by simpa [gpOf, hr', hr2] using n34)
    exact fun i j h => hs (congrArg Fin.val h)
  · intro i
    fin_cases i
    · simpa [gpOf, hr', hr2] using e0
    · simpa [gpOf, hr', hr2] using e1
    · simpa [gpOf, hr', hr2] using e2
    · simpa [gpOf, hr', hr2] using e3
    · simpa [gpOf, hr', hr2] using e4

theorem d2Ok_of_G (h yp : V5) (r : List ℤ) (g z : ℕ → ℤ) (f : FC)
    (hr : ∀ k, k < 64 → r.getD k 0 = g k)
    (hz : ∀ i : Fin 5, yp i = z (4 + i.val))
    (hf : f.h0 = h 0 ∧ f.h1 = h 1 ∧ f.h2 = h 2 ∧ f.h3 = h 3 ∧ f.h4 = h 4)
    (hc : recClassG f g z = true) :
    d2Ok ⟨[h, cY r], [h, yp], gpOf r, mat2 r 56, mat2 r 60⟩ = true := by
  obtain ⟨hf0, hf1, hf2, hf3, hf4⟩ := hf
  have hr' := hr
  have hr2 : ∀ k, k < 64 → r[k]?.getD 0 = g k := fun k hk => by rw [← hr k hk]; simp
  have hY : ∀ s : Fin 5, cY r s = g (4 + s.val) := fun s => hr (4 + s.val) (by have := s.isLt; omega)
  simp only [recClassG, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, and_assoc, hf0, hf1, hf2, hf3, hf4,
    sel5_mod, sel5_modg] at hc
  obtain ⟨n01, n02, n03, n04, n12, n13, n14, n23, n24, n34, ε0, ε1, ε2, ε3, ε4, hA, a0, a1, a2, a3, a4,
    c0, c1, c2, c3, c4, v0, v1, v2, v3, v4, w0, w1, w2, w3, w4⟩ := hc
  have hg : gOk (gpOf r) := gp_ok r g hr' hr2 n01 n02 n03 n04 n12 n13 n14 n23 n24 n34 ε0 ε1 ε2 ε3 ε4
  have key : ∀ (x : V5) (c : Fin 5), (gSP (gpOf r) hg).act x c =
      g (51 + c.val) * x ⟨(g (46 + c.val)).toNat % 5, Nat.mod_lt _ (by norm_num)⟩ := by
    intro x c
    have e1 := hr' (51 + c.val) (by have := c.isLt; omega)
    have e2 := hr' (46 + c.val) (by have := c.isLt; omega)
    have e3 : (⟨(r.getD (46 + c.val) 0).toNat % 5, Nat.mod_lt _ (by norm_num)⟩ : Fin 5) =
        ⟨(g (46 + c.val)).toNat % 5, Nat.mod_lt _ (by norm_num)⟩ := Fin.ext (by simp only [e2])
    show r.getD (51 + c.val) 0 * x ⟨(r.getD (46 + c.val) 0).toNat % 5, _⟩ = _
    rw [e1, e3]
  have keyy : ∀ c : Fin 5, (gSP (gpOf r) hg).act (cY r) c = g (51 + c.val) * g (4 + (g (46 + c.val)).toNat % 5) := by
    intro c
    rw [key]
    exact congrArg _ (hY _)
  unfold d2Ok
  rw [dif_pos hg]
  apply decide_eq_true
  have m00 : matL (mat2 r 56) 0 0 = g 56 := by simp [matL, mat2, hr', hr2]
  have m01 : matL (mat2 r 56) 0 1 = g 57 := by simp [matL, mat2, hr', hr2]
  have m10 : matL (mat2 r 56) 1 0 = g 58 := by simp [matL, mat2, hr', hr2]
  have m11 : matL (mat2 r 56) 1 1 = g 59 := by simp [matL, mat2, hr', hr2]
  have p00 : matL (mat2 r 60) 0 0 = g 60 := by simp [matL, mat2, hr', hr2]
  have p01 : matL (mat2 r 60) 0 1 = g 61 := by simp [matL, mat2, hr', hr2]
  have p10 : matL (mat2 r 60) 1 0 = g 62 := by simp [matL, mat2, hr', hr2]
  have p11 : matL (mat2 r 60) 1 1 = g 63 := by simp [matL, mat2, hr', hr2]
  have hz' : ∀ c : Fin 5, yp c = z (4 + c.val) := hz
  refine ⟨?_, ?_⟩
  · apply chain1_core
    rcases hA with ⟨x0, x1, x2, x3, x4⟩ | ⟨x0, x1, x2, x3, x4⟩
    · left
      intro c
      rw [key]
      fin_cases c <;> simp <;>
        first | linarith only [x0] | linarith only [x1] | linarith only [x2] | linarith only [x3] | linarith only [x4]
    · right
      intro c
      rw [key]
      fin_cases c <;> simp <;>
        first | linarith only [x0] | linarith only [x1] | linarith only [x2] | linarith only [x3] | linarith only [x4]
  · apply leq_core
    · intro c
      rw [key, m00, m01, hz']
      fin_cases c <;> simp <;>
        first | linarith only [a0] | linarith only [a1] | linarith only [a2] | linarith only [a3] | linarith only [a4]
    · intro c
      rw [keyy, m10, m11, hz']
      fin_cases c <;> simp <;>
        first | linarith only [c0] | linarith only [c1] | linarith only [c2] | linarith only [c3] | linarith only [c4]
    · intro c
      rw [p00, p01, key, keyy]
      fin_cases c <;> simp <;>
        first | linarith only [v0] | linarith only [v1] | linarith only [v2] | linarith only [v3] | linarith only [v4]
    · intro c
      rw [hz', p10, p11, key, keyy]
      fin_cases c <;> simp <;>
        first | linarith only [w0] | linarith only [w1] | linarith only [w2] | linarith only [w3] | linarith only [w4]

/-! ## Unpacking -/

theorem unpack_getD (n k : ℕ) (hk : k < 64) : (unpackRec n).getD k 0 = dgI n k := by
  unfold unpackRec dgI
  simp [List.getD_eq_getElem?_getD, hk]

theorem getD_map_unpack (LN : List ℕ) (i : ℕ) (hi : i < LN.length) :
    (LN.map unpackRec).getD i [] = unpackRec (LN.getD i 0) := by
  simp [List.getD_eq_getElem?_getD, hi]

/-- **The bridge.** The flat packed-Nat record check accepting a record implies the original `recOkB` on the unpacked list. -/
theorem recOkN_sound (n : NodeW 1 4) (bn bd : ℤ) (LN : List ℕ) (rN : ℕ)
    (h : recN (FC.ofCtx (ctxOf n bn bd)) LN rN = true) :
    recOkB n (LN.map unpackRec) (unpackRec rN) = true := by
  have hr : ∀ k, k < 64 → (unpackRec rN).getD k 0 = dgI rN k := fun k hk => unpack_getD rN k hk
  have e1 : recFactsN (FC.ofCtx (ctxOf n bn bd)) rN = recFactsG (FC.ofCtx (ctxOf n bn bd)) (dgI rN) := rfl
  unfold recN at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨hf, hl⟩, hc⟩ := h
  rw [e1] at hf
  have hrep : cRep (unpackRec rN) = (dgI rN 45).toNat := by
    unfold cRep; rw [unpack_getD rN 45 (by norm_num)]
  unfold recOkB
  simp only [Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨recFactsG_sound n bn bd _ _ hr hf, ?_⟩, ?_⟩
  · rw [hrep, List.length_map]; exact hl
  · have hcl : recClassN (FC.ofCtx (ctxOf n bn bd)) LN rN =
        recClassG (FC.ofCtx (ctxOf n bn bd)) (dgI rN) (fun k => dgI (LN.getD (dgI rN 45).toNat 0) k) := rfl
    rw [hcl] at hc
    unfold classRaw
    rw [hrep]
    have := d2Ok_of_G (hN n.rows 0) (cY ((LN.map unpackRec).getD (dgI rN 45).toNat [])) (unpackRec rN) (dgI rN)
      (fun k => dgI (LN.getD (dgI rN 45).toNat 0) k) (FC.ofCtx (ctxOf n bn bd)) hr
      (fun i => by
        rw [getD_map_unpack LN _ hl]
        show (unpackRec (LN.getD (dgI rN 45).toNat 0)).getD (4 + i.val) 0 = _
        exact unpack_getD _ _ (by have := i.isLt; omega))
      ⟨rfl, rfl, rfl, rfl, rfl⟩ hc
    simpa using this

end L5S4
end LRSpectrumFull

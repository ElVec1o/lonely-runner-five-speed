/-
# L5S4.GFlat : flat-Int child filters of a depth-1 node and the slice-list completeness theorem (case-tree certificate, part 7)

Part 6 evaluated the filters through `Finset` sums over `Fin 5` and `Decidable` instances of `FirstPos`, `GcdOne`, `eiBad`
(measured per-box-point costs were the reason for the change).  Here the node data is flattened into the structure `FC` of 47
integers (one-time bridge `FC.ofCtx`), and every filter is a plain `Int`/`Nat` expression:

* `fpF`, `gcdF` (`Nat.gcd`, GMP-accelerated), `ballF`, `eiF`, `greedyF` (the 2x2 box search `shortB`, with flat `a, p, q`);
* `passPoint` = their conjunction; `passList` = the passing `(t2, t3)` of one slice; `sliceF` compares it with the stored records
  of the slice (one `List` equality instead of a membership search per point).

Soundness in the direction list completeness needs: `passPoint_of_childPass` (`ChildPass n y -> passPoint ... = true`) and
`child_list_completeF` (same conclusion as `child_list_complete`).  The soundness direction needs no relation between the box
bounds of the Rust generator and the integer square root used here: a found short vector is a witness whatever the box is.

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.CheckChildRec

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

structure FC where
  h0 : ℤ
  h1 : ℤ
  h2 : ℤ
  h3 : ℤ
  h4 : ℤ
  b00 : ℤ
  b01 : ℤ
  b02 : ℤ
  b03 : ℤ
  b04 : ℤ
  b10 : ℤ
  b11 : ℤ
  b12 : ℤ
  b13 : ℤ
  b14 : ℤ
  b20 : ℤ
  b21 : ℤ
  b22 : ℤ
  b23 : ℤ
  b24 : ℤ
  b30 : ℤ
  b31 : ℤ
  b32 : ℤ
  b33 : ℤ
  b34 : ℤ
  r00 : ℤ
  r01 : ℤ
  r02 : ℤ
  r03 : ℤ
  r04 : ℤ
  r10 : ℤ
  r11 : ℤ
  r12 : ℤ
  r13 : ℤ
  r14 : ℤ
  r20 : ℤ
  r21 : ℤ
  r22 : ℤ
  r23 : ℤ
  r24 : ℤ
  r30 : ℤ
  r31 : ℤ
  r32 : ℤ
  r33 : ℤ
  r34 : ℤ
  bn : ℤ
  bd : ℤ

def FC.ofCtx (c : Ctx) : FC :=
  ⟨c.h 0, c.h 1, c.h 2, c.h 3, c.h 4,
   c.b 0 0, c.b 0 1, c.b 0 2, c.b 0 3, c.b 0 4, c.b 1 0, c.b 1 1, c.b 1 2, c.b 1 3, c.b 1 4,
   c.b 2 0, c.b 2 1, c.b 2 2, c.b 2 3, c.b 2 4, c.b 3 0, c.b 3 1, c.b 3 2, c.b 3 3, c.b 3 4,
   c.r 0 0, c.r 0 1, c.r 0 2, c.r 0 3, c.r 0 4, c.r 1 0, c.r 1 1, c.r 1 2, c.r 1 3, c.r 1 4,
   c.r 2 0, c.r 2 1, c.r 2 2, c.r 2 3, c.r 2 4, c.r 3 0, c.r 3 1, c.r 3 2, c.r 3 3, c.r 3 4,
   c.bn, c.bd⟩

def FC.aa (f : FC) : ℤ := f.h0 * f.h0 + f.h1 * f.h1 + f.h2 * f.h2 + f.h3 * f.h3 + f.h4 * f.h4

/-- the lifted row `y` (`liftY`), as five integers. -/
def lift5 (f : FC) (t0 t1 t2 t3 : ℤ) : ℤ × ℤ × ℤ × ℤ × ℤ :=
  let y0 := t0 * f.r00 + t1 * f.r10 + t2 * f.r20 + t3 * f.r30
  let y1 := t0 * f.r01 + t1 * f.r11 + t2 * f.r21 + t3 * f.r31
  let y2 := t0 * f.r02 + t1 * f.r12 + t2 * f.r22 + t3 * f.r32
  let y3 := t0 * f.r03 + t1 * f.r13 + t2 * f.r23 + t3 * f.r33
  let y4 := t0 * f.r04 + t1 * f.r14 + t2 * f.r24 + t3 * f.r34
  let k := liftQ f.aa (f.h0 * y0 + f.h1 * y1 + f.h2 * y2 + f.h3 * y3 + f.h4 * y4)
  (y0 - k * f.h0, y1 - k * f.h1, y2 - k * f.h2, y3 - k * f.h3, y4 - k * f.h4)

def ballF (f : FC) (t0 t1 t2 t3 : ℤ) : Bool :=
  let y := lift5 f t0 t1 t2 t3
  let s := f.h0 * y.1 + f.h1 * y.2.1 + f.h2 * y.2.2.1 + f.h3 * y.2.2.2.1 + f.h4 * y.2.2.2.2
  decide ((f.aa * (y.1 * y.1 + y.2.1 * y.2.1 + y.2.2.1 * y.2.2.1 + y.2.2.2.1 * y.2.2.2.1 + y.2.2.2.2 * y.2.2.2.2)
    - s * s) * f.bd < f.bn * f.aa)

def greedyF (f : FC) (t0 t1 t2 t3 : ℤ) : Bool :=
  let y := lift5 f t0 t1 t2 t3
  shortB f.aa (f.h0 * y.1 + f.h1 * y.2.1 + f.h2 * y.2.2.1 + f.h3 * y.2.2.2.1 + f.h4 * y.2.2.2.2)
    (y.1 * y.1 + y.2.1 * y.2.1 + y.2.2.1 * y.2.2.1 + y.2.2.2.1 * y.2.2.2.1 + y.2.2.2.2 * y.2.2.2.2)

def fpF (t0 t1 t2 t3 : ℤ) : Bool :=
  decide (0 < t0) || (decide (t0 = 0) && (decide (0 < t1) || (decide (t1 = 0) &&
    (decide (0 < t2) || (decide (t2 = 0) && decide (0 < t3))))))

def gcdF (t0 t1 t2 t3 : ℤ) : Bool :=
  Nat.beq (Nat.gcd (Nat.gcd (Nat.gcd t0.natAbs t1.natAbs) t2.natAbs) t3.natAbs) 1

def eiAt (b0 b1 b2 b3 t0 t1 t2 t3 : ℤ) : Bool :=
  decide (b0 * t1 = b1 * t0) && decide (b0 * t2 = b2 * t0) && decide (b0 * t3 = b3 * t0) &&
  decide (b1 * t2 = b2 * t1) && decide (b1 * t3 = b3 * t1) && decide (b2 * t3 = b3 * t2)

def eiF (f : FC) (t0 t1 t2 t3 : ℤ) : Bool :=
  eiAt f.b00 f.b10 f.b20 f.b30 t0 t1 t2 t3 || eiAt f.b01 f.b11 f.b21 f.b31 t0 t1 t2 t3 ||
  eiAt f.b02 f.b12 f.b22 f.b32 t0 t1 t2 t3 || eiAt f.b03 f.b13 f.b23 f.b33 t0 t1 t2 t3 ||
  eiAt f.b04 f.b14 f.b24 f.b34 t0 t1 t2 t3

def passPoint (f : FC) (t0 t1 t2 t3 : ℤ) : Bool :=
  fpF t0 t1 t2 t3 && gcdF t0 t1 t2 t3 && ballF f t0 t1 t2 t3 && !eiF f t0 t1 t2 t3 && !greedyF f t0 t1 t2 t3

/-! ## Soundness of each flat test -/

theorem fpF_of {t : Fin 4 → ℤ} (h : FirstPos t) : fpF (t 0) (t 1) (t 2) (t 3) = true := by
  obtain ⟨m, hm, hz⟩ := h
  fin_cases m
  · simp only [Fin.zero_eta, Fin.isValue] at hm
    simp [fpF, hm]
  · have h0 : t 0 = 0 := hz 0 (by decide)
    simp only [Fin.mk_one, Fin.isValue] at hm
    simp [fpF, h0, hm]
  · have h0 : t 0 = 0 := hz 0 (by decide)
    have h1 : t 1 = 0 := hz 1 (by decide)
    simp only [Fin.reduceFinMk, Fin.isValue] at hm
    simp [fpF, h0, h1, hm]
  · have h0 : t 0 = 0 := hz 0 (by decide)
    have h1 : t 1 = 0 := hz 1 (by decide)
    have h2 : t 2 = 0 := hz 2 (by decide)
    simp only [Fin.reduceFinMk, Fin.isValue] at hm
    simp [fpF, h0, h1, h2, hm]

theorem gcdF_of {t : Fin 4 → ℤ} (h : GcdOne t) : gcdF (t 0) (t 1) (t 2) (t 3) = true := by
  obtain ⟨u, hu⟩ := bezout_of_gcd t h
  set g : ℕ := Nat.gcd (Nat.gcd (Nat.gcd (t 0).natAbs (t 1).natAbs) (t 2).natAbs) (t 3).natAbs with hg
  have d3 : g ∣ (t 3).natAbs := Nat.gcd_dvd_right _ _
  have g3 : g ∣ Nat.gcd (Nat.gcd (t 0).natAbs (t 1).natAbs) (t 2).natAbs := Nat.gcd_dvd_left _ _
  have g2 : g ∣ Nat.gcd (t 0).natAbs (t 1).natAbs :=
    g3.trans (Nat.gcd_dvd_left (Nat.gcd (t 0).natAbs (t 1).natAbs) (t 2).natAbs)
  have d2 : g ∣ (t 2).natAbs := g3.trans (Nat.gcd_dvd_right (Nat.gcd (t 0).natAbs (t 1).natAbs) (t 2).natAbs)
  have d1 : g ∣ (t 1).natAbs := g2.trans (Nat.gcd_dvd_right (t 0).natAbs (t 1).natAbs)
  have d0 : g ∣ (t 0).natAbs := g2.trans (Nat.gcd_dvd_left (t 0).natAbs (t 1).natAbs)
  have e : ∀ x : ℤ, g ∣ x.natAbs → (g : ℤ) ∣ x := fun x hx => Int.natCast_dvd.2 hx
  have hs : (g : ℤ) ∣ ∑ i, t i * u i := by
    simp only [Fin.sum_univ_four]
    exact dvd_add (dvd_add (dvd_add (Dvd.dvd.mul_right (e _ d0) _) (Dvd.dvd.mul_right (e _ d1) _))
      (Dvd.dvd.mul_right (e _ d2) _)) (Dvd.dvd.mul_right (e _ d3) _)
  rw [hu] at hs
  have : g ∣ 1 := by exact_mod_cast hs
  have : g = 1 := Nat.dvd_one.1 this
  unfold gcdF
  rw [← hg, this]; rfl

theorem eiF_imp {c : Ctx} {t : Fin 4 → ℤ} (h : eiF (FC.ofCtx c) (t 0) (t 1) (t 2) (t 3) = true) : eiBad c.b t := by
  have key : ∀ i : Fin 5, eiAt (c.b 0 i) (c.b 1 i) (c.b 2 i) (c.b 3 i) (t 0) (t 1) (t 2) (t 3) = true →
      ∀ a a' : Fin 4, a < a' → c.b a i * t a' = c.b a' i * t a := by
    intro i hi a a' hlt
    simp only [eiAt, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨⟨⟨⟨h01, h02⟩, h03⟩, h12⟩, h13⟩, h23⟩ := hi
    fin_cases a <;> fin_cases a' <;> simp at hlt ⊢ <;> first | exact h01 | exact h02 | exact h03 | exact h12 | exact h13 | exact h23
  simp only [eiF, FC.ofCtx, Bool.or_eq_true] at h
  rcases h with ((((h | h) | h) | h) | h)
  · exact ⟨0, key 0 h⟩
  · exact ⟨1, key 1 h⟩
  · exact ⟨2, key 2 h⟩
  · exact ⟨3, key 3 h⟩
  · exact ⟨4, key 4 h⟩

theorem ballF_eq (c : Ctx) (t : Fin 4 → ℤ) : ballF (FC.ofCtx c) (t 0) (t 1) (t 2) (t 3) = ballB c t := by
  unfold ballF ballB lift5 liftY y0Of liftQ Ctx.a dot FC.ofCtx FC.aa
  simp only [Fin.sum_univ_five, sq]
  try rfl

theorem greedyF_eq (c : Ctx) (t : Fin 4 → ℤ) : greedyF (FC.ofCtx c) (t 0) (t 1) (t 2) (t 3) = greedyB c t := by
  unfold greedyF greedyB lift5 liftY y0Of liftQ Ctx.a dot FC.ofCtx FC.aa
  simp only [Fin.sum_univ_five]

theorem passPoint_of_childPass (n : NodeW 1 4) (bn bd : ℤ) (hbd : 0 < bd)
    (hrad : radFrac (Cq (1 + 1)) n.wit n.rows 1 n.rk = (bn : ℚ) / bd) (y : V5) (hp : ChildPass n y) :
    passPoint (FC.ofCtx (ctxOf n bn bd)) (tvec n.b y 0) (tvec n.b y 1) (tvec n.b y 2) (tvec n.b y 3) = true := by
  have h := childPass_imp_passB n bn bd hbd hrad y hp
  unfold passB at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hfp, hball⟩, hgcd⟩, hei⟩, hgr⟩ := h
  have e1 := fpF_of hfp
  have e2 := gcdF_of hgcd
  have e3 := ballF_eq (ctxOf n bn bd) (tvec n.b y)
  have e5 := greedyF_eq (ctxOf n bn bd) (tvec n.b y)
  have e4 : eiF (FC.ofCtx (ctxOf n bn bd)) (tvec n.b y 0) (tvec n.b y 1) (tvec n.b y 2) (tvec n.b y 3) = false := by
    by_contra hne
    have hei' : ¬ eiBad (ctxOf n bn bd).b (tvec n.b y) := by simpa using hei
    exact hei' (eiF_imp (by simpa using hne))
  unfold passPoint
  rw [e1, e2, e3, hball, e4, e5, hgr]
  rfl

/-! ## Slice lists and completeness -/

def passList (f : FC) (T2 T3 t0 t1 : ℤ) : List (ℤ × ℤ) :=
  (rngI T2).flatMap fun t2 => (rngI T3).filterMap fun t3 => if passPoint f t0 t1 t2 t3 then some (t2, t3) else none

def recPair (r : List ℤ) : ℤ × ℤ := (r.getD 2 0, r.getD 3 0)

def sliceF (f : FC) (T2 T3 : ℤ) (g : ℤ × List (List ℤ)) (t1 : ℤ) : Bool :=
  decide (passList f T2 T3 g.1 t1 = (g.2.filter fun r => decide (r.getD 0 0 = g.1) && decide (r.getD 1 0 = t1)).map recPair)

theorem mem_passList {f : FC} {T2 T3 t0 t1 t2 t3 : ℤ} (h2 : |t2| ≤ T2) (h3 : |t3| ≤ T3)
    (hT2 : 0 ≤ T2) (hT3 : 0 ≤ T3) (hp : passPoint f t0 t1 t2 t3 = true) : (t2, t3) ∈ passList f T2 T3 t0 t1 := by
  unfold passList
  rw [List.mem_flatMap]
  refine ⟨t2, (mem_rngI hT2).2 h2, ?_⟩
  rw [List.mem_filterMap]
  exact ⟨t3, (mem_rngI hT3).2 h3, by simp [hp]⟩

/-- **List completeness, flat version.** Same conclusion as `child_list_complete`. -/
theorem child_list_completeF (n : NodeW 1 4) (bn bd : ℤ) (hbd : 0 < bd)
    (hrad : radFrac (Cq (1 + 1)) n.wit n.rows 1 n.rk = (bn : ℚ) / bd)
    (G : List (ℤ × List (List ℤ))) (hkeys : G.map Prod.fst = rngI (tmaxOf (ctxOf n bn bd) 0))
    (T2 T3 : ℤ) (hT2 : tmaxOf (ctxOf n bn bd) 2 = T2) (hT3 : tmaxOf (ctxOf n bn bd) 3 = T3)
    (hs : ∀ g ∈ G, ∀ t1 ∈ rngI (tmaxOf (ctxOf n bn bd) 1), sliceF (FC.ofCtx (ctxOf n bn bd)) T2 T3 g t1 = true)
    (y : V5) (hp : ChildPass n y) :
    ∃ g ∈ G, ∃ r ∈ g.2, recT r = tvec n.b y := by
  have hpt := passPoint_of_childPass n bn bd hbd hrad y hp
  have hbox : ∀ i, |tvec n.b y i| ≤ tmaxOf (ctxOf n bn bd) i := fun i => by
    have hq : qform n.b y * bd < bn * (gramK n.b).det := by
      rw [det_gramK]; exact ball_of_pass n bn bd hbd hrad y hp
    have := box_covers (by norm_num) n.id y i bn bd hbd hq
    simpa [tmaxOf, ctxOf, gramK] using this
  have h0 : tvec n.b y 0 ∈ G.map Prod.fst := by
    rw [hkeys, mem_rngI (tmax_nonneg _ 0)]; exact hbox 0
  obtain ⟨g, hg, hg0⟩ := List.mem_map.1 h0
  have h1 := hs g hg (tvec n.b y 1) ((mem_rngI (tmax_nonneg _ 1)).2 (hbox 1))
  unfold sliceF at h1
  have h1' := of_decide_eq_true h1
  have hT2' : 0 ≤ T2 := hT2 ▸ tmax_nonneg _ 2
  have hT3' : 0 ≤ T3 := hT3 ▸ tmax_nonneg _ 3
  have hmem := mem_passList (f := FC.ofCtx (ctxOf n bn bd)) (t0 := g.1) (t1 := tvec n.b y 1)
    (hT2 ▸ hbox 2) (hT3 ▸ hbox 3) hT2' hT3' (by rw [hg0]; exact hpt)
  rw [h1'] at hmem
  obtain ⟨r, hr, hrp⟩ := List.mem_map.1 hmem
  rw [List.mem_filter] at hr
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hr
  obtain ⟨hrg, hr0, hr1⟩ := hr
  refine ⟨g, hg, r, hrg, ?_⟩
  unfold recPair at hrp
  have hr2 : r.getD 2 0 = tvec n.b y 2 := congrArg Prod.fst hrp
  have hr3 : r.getD 3 0 = tvec n.b y 3 := congrArg Prod.snd hrp
  funext i; fin_cases i
  · show r.getD 0 0 = _; rw [hr0, hg0]; rfl
  · exact hr1
  · exact hr2
  · exact hr3

end L5S4
end LRSpectrumFull

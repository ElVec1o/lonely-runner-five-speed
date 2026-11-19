/-
# L5S4.CheckChildFilt : the Boolean child filters of a depth-1 node and their necessity theorem

Case-tree certificate, part 6.  For a depth-1 node `n : NodeW 1 4` (`d = 4`, `j = 1`) the generator's
child loop is a Boolean function of the coordinates `t = b y`:

* `liftY` : the row `y` of the generator (`lib.rs::lift`: `∑ t_k r_k` reduced mod `l_0`), `tvec b (liftY t) = t`;
* `fpB` (first nonzero coordinate positive), `ballB` (`q·bd < bn·g`, with `q = a·|y|² - (h·y)²`, `a = |h|²`,
  `g = a`), `gcdB`, `eiB`, `greedyB` (`exists_shorter` of the Gram matrix of `(h, y)` against `a`: a box search);
* `passB` = their conjunction (cheap tests first), `boxOk` = the list-completeness checker: every `t` of the box
  `|t_i| ≤ isqrt(bn a_ii / bd)` passing `passB` appears in the stored list (grouped by `t0`).

Soundness in the direction the completeness induction needs (`ChildPass n y → passB (b y) = true`, so a rejected
candidate is never a child): `childPass_imp_passB`; with `boxOk`, `child_list_complete`: every `y` with `ChildPass n y`
has its coordinates `b y` stored.  Representative invariance for `j = 1` (`ChildPass n y` vs the generator's lift of
`b y`) is proved here (`greedy_of_pass`: the shift `y_r = y + κ h` and `existsShorter_iff`).

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.ChildStep

namespace LRSpectrumFull
namespace L5S4

open Matrix Finset LRSpectrumFull.L5S3

/-! ## 1. Range lists -/

def rngI (T : ℤ) : List ℤ := (List.range (2 * T.toNat + 1)).map fun k : ℕ => ((k : ℤ) - T)

theorem mem_rngI {T x : ℤ} (hT : 0 ≤ T) : x ∈ rngI T ↔ |x| ≤ T := by
  unfold rngI
  simp only [List.mem_map, List.mem_range]
  rw [abs_le]
  have hT' : ((T.toNat : ℕ) : ℤ) = T := Int.toNat_of_nonneg hT
  constructor
  · rintro ⟨k, hk, rfl⟩
    have : (k : ℤ) < 2 * (T.toNat : ℤ) + 1 := by exact_mod_cast hk
    omega
  · intro h
    have h1 : (x + T).toNat < 2 * T.toNat + 1 := by omega
    exact ⟨(x + T).toNat, h1, by omega⟩

/-! ## 2. The lift and the Boolean filters -/

structure Ctx where
  h : V5
  b : Fin 4 → V5
  r : Fin 4 → V5
  bn : ℤ
  bd : ℤ

def Ctx.a (c : Ctx) : ℤ := dot c.h c.h

/-- `lib.rs::rdiv` (`a > 0`): rounded quotient. -/
def liftQ (a p : ℤ) : ℤ := (2 * p + a) / (2 * a)

def y0Of (r : Fin 4 → V5) (t : Fin 4 → ℤ) : V5 := fun c => t 0 * r 0 c + t 1 * r 1 c + t 2 * r 2 c + t 3 * r 3 c

/-- `lib.rs::lift` for `j = 1`. -/
def liftY (r : Fin 4 → V5) (h : V5) (t : Fin 4 → ℤ) : V5 :=
  fun c => y0Of r t c - liftQ (dot h h) (dot h (y0Of r t)) * h c

instance (t : Fin 4 → ℤ) : Decidable (FirstPos t) := by unfold FirstPos; infer_instance
instance {d : ℕ} (t : Fin d → ℤ) : Decidable (GcdOne t) := by unfold GcdOne; infer_instance
instance {d : ℕ} (b : Fin d → V5) (t : Fin d → ℤ) : Decidable (eiBad b t) := by unfold eiBad; infer_instance

def ballB (c : Ctx) (t : Fin 4 → ℤ) : Bool :=
  decide ((c.a * dot (liftY c.r c.h t) (liftY c.r c.h t) - dot c.h (liftY c.r c.h t) ^ 2) * c.bd < c.bn * c.a)

/-- Box search for a nonzero `(c0, c1)` with `a c0² + 2 p c0 c1 + q c1² < a` (Gram `[[a,p],[p,q]]`, bound `a`). -/
def shortB (a p q : ℤ) : Bool :=
  (rngI (isqrtI ((max (a - 1) 0 * q) / (a * q - p ^ 2)))).any fun c0 =>
    (rngI (isqrtI ((max (a - 1) 0 * a) / (a * q - p ^ 2)))).any fun c1 =>
      (decide (c0 ≠ 0) || decide (c1 ≠ 0)) && decide (a * c0 * c0 + 2 * p * c0 * c1 + q * c1 * c1 < a)

def greedyB (c : Ctx) (t : Fin 4 → ℤ) : Bool :=
  shortB c.a (dot c.h (liftY c.r c.h t)) (dot (liftY c.r c.h t) (liftY c.r c.h t))

def passB (c : Ctx) (t : Fin 4 → ℤ) : Bool :=
  decide (FirstPos t) && ballB c t && decide (GcdOne t) && !decide (eiBad c.b t) && !greedyB c t

theorem shortB_exists {a p q : ℤ} (h : shortB a p q = true) :
    ∃ c0 c1 : ℤ, (c0 ≠ 0 ∨ c1 ≠ 0) ∧ a * c0 * c0 + 2 * p * c0 * c1 + q * c1 * c1 < a := by
  unfold shortB at h
  simp only [List.any_eq_true, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at h
  obtain ⟨c0, -, c1, -, h1, h2⟩ := h
  exact ⟨c0, c1, h1, h2⟩

/-! ## 3. The node facts used by the filters -/

def ctxOf (n : NodeW 1 4) (bn bd : ℤ) : Ctx := ⟨hN n.rows 0, n.b, n.r, bn, bd⟩

theorem nid_bl (n : NodeW 1 4) (i : Fin 4) : dot (n.b i) (hN n.rows 0) = 0 := by
  simpa using n.id.bl i 0

theorem tvec_liftY (n : NodeW 1 4) (t : Fin 4 → ℤ) : tvec n.b (liftY n.r (hN n.rows 0) t) = t := by
  funext i
  have h1 : tvec n.b (fun a => ∑ k, t k * n.r k a) = t := tvec_lift0 n.id t
  have h2 : dot (n.b i) (y0Of n.r t) = t i := by
    have := congrFun h1 i
    simpa [tvec, y0Of, Fin.sum_univ_four] using this
  unfold tvec liftY
  have h3 : dot (n.b i) (fun c => y0Of n.r t c - liftQ (dot (hN n.rows 0) (hN n.rows 0))
      (dot (hN n.rows 0) (y0Of n.r t)) * hN n.rows 0 c)
      = dot (n.b i) (y0Of n.r t) - liftQ (dot (hN n.rows 0) (hN n.rows 0)) (dot (hN n.rows 0) (y0Of n.r t))
        * dot (n.b i) (hN n.rows 0) := by
    unfold dot
    simp only [mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
    exact congrArg₂ _ rfl (Finset.sum_congr rfl (fun _ _ => by ring))
  rw [h3, nid_bl, h2]; ring

theorem det_gramK (n : NodeW 1 4) : (gramK n.b).det = dot (hN n.rows 0) (hN n.rows 0) := by
  have h := gF_compl (by norm_num) n.id
  have e : (gramK n.b).det = gF n.b := rfl
  rw [e, h]
  unfold gF
  rw [Matrix.det_unique]
  simp [Matrix.of_apply]

theorem snoc_rows (n : NodeW 1 4) (y : V5) :
    rowsR (setRow n.rows 1 y) 2 = Fin.snoc (α := fun _ => V5) (fun i : Fin 1 => hN n.rows i.val) y := by
  funext i
  fin_cases i
  · simp [rowsR, setRow, hN, Fin.snoc]
  · simp [rowsR, setRow, hN, Fin.snoc]

theorem qform_eq (n : NodeW 1 4) (y : V5) :
    qform n.b y = dot (hN n.rows 0) (hN n.rows 0) * dot y y - dot (hN n.rows 0) y * dot (hN n.rows 0) y := by
  rw [← gF_snoc (by norm_num) n.id y]
  unfold gF
  rw [Matrix.det_fin_two]
  simp [Fin.snoc, dot_comm' y (hN n.rows 0)]

theorem gF_pos_of_rinv {k : ℕ} (f s' : Fin k → V5) (hs : ∀ i m, dot (f i) (s' m) = if i = m then 1 else 0) :
    0 < gF f := by
  have h1 : mR f * mC s' = 1 := by
    rw [mR_mul_mC]; ext i m; simp [hs, Matrix.one_apply]
  have := det_gram_pos_Z (mR f) (mC s') h1
  rw [mR_mul_mR_T] at this
  exact this

theorem qform_pos (n : NodeW 1 4) (y : V5) (hg : GcdOne (tvec n.b y)) : 0 < qform n.b y := by
  obtain ⟨s', hs'⟩ := ext_ls n.id y hg
  rw [← gF_snoc (by norm_num) n.id y]
  exact gF_pos_of_rinv _ s' hs'

theorem qform_congr (n : NodeW 1 4) {y y' : V5} (h : tvec n.b y = tvec n.b y') : qform n.b y = qform n.b y' := by
  unfold qform; rw [h]

/-! ## 4. The radius test -/

theorem ball_of_pass (n : NodeW 1 4) (bn bd : ℤ) (hbd : 0 < bd)
    (hrad : radFrac (Cq (1 + 1)) n.wit n.rows 1 n.rk = (bn : ℚ) / bd) (y : V5) (hp : ChildPass n y) :
    qform n.b y * bd < bn * dot (hN n.rows 0) (hN n.rows 0) := by
  have h := hp.2.2.2.2.2
  rw [det_gramK] at h
  set R := radFrac (Cq (1 + 1)) n.wit n.rows 1 n.rk with hR
  set G := dot (hN n.rows 0) (hN n.rows 0) with hG
  have hden : (0 : ℤ) < (R.den : ℤ) := by exact_mod_cast R.den_pos
  have hbdq : (bd : ℚ) ≠ 0 := by exact_mod_cast hbd.ne'
  have hdq : (R.den : ℚ) ≠ 0 := by exact_mod_cast R.den_nz
  have e : R.num * bd = bn * (R.den : ℤ) := by
    have h1 : (R.num : ℚ) / (R.den : ℚ) = (bn : ℚ) / bd := by rw [Rat.num_div_den, hrad]
    rw [div_eq_div_iff hdq hbdq] at h1
    exact_mod_cast h1
  have h1 : (qform n.b y * (R.den : ℤ)) * bd < (R.num * G) * bd := mul_lt_mul_of_pos_right h hbd
  have h3 : (R.num * G) * bd = (bn * G) * (R.den : ℤ) := by linear_combination G * e
  have h4 : (qform n.b y * (R.den : ℤ)) * bd = (qform n.b y * bd) * (R.den : ℤ) := by ring
  rw [h3, h4] at h1
  exact lt_of_mul_lt_mul_right h1 hden.le

/-! ## 5. Representative invariance for `j = 1` and the greedy test -/

theorem comb_shift (n : NodeW 1 4) (y yr : V5) (c0 c1 κ : ℤ)
    (hy : ∀ a, yr a = y a + κ * hN n.rows 0 a) :
    dot (comb (rowsR (setRow n.rows 1 y) 2) ![c0 + c1 * κ, c1]) (comb (rowsR (setRow n.rows 1 y) 2) ![c0 + c1 * κ, c1])
      = dot (hN n.rows 0) (hN n.rows 0) * c0 * c0 + 2 * dot (hN n.rows 0) yr * c0 * c1 + dot yr yr * c1 * c1 := by
  have e : ∀ a, comb (rowsR (setRow n.rows 1 y) 2) ![c0 + c1 * κ, c1] a = c0 * hN n.rows 0 a + c1 * yr a := by
    intro a
    simp [comb, Fin.sum_univ_two, rowsR, setRow, hN, hy a]
    ring
  have e2 : comb (rowsR (setRow n.rows 1 y) 2) ![c0 + c1 * κ, c1] = fun a => c0 * hN n.rows 0 a + c1 * yr a :=
    funext e
  rw [e2]
  unfold dot
  simp only [Fin.sum_univ_five]
  ring

theorem greedy_of_pass (n : NodeW 1 4) (bn bd : ℤ) (y : V5) (hp : ChildPass n y) :
    greedyB (ctxOf n bn bd) (tvec n.b y) = false := by
  by_contra hne
  have hT : greedyB (ctxOf n bn bd) (tvec n.b y) = true := by simpa using hne
  unfold greedyB at hT
  obtain ⟨c0, c1, hc, hlt⟩ := shortB_exists hT
  set yr := liftY n.r (hN n.rows 0) (tvec n.b y) with hyr
  have htv : tvec n.b yr = tvec n.b y := tvec_liftY n (tvec n.b y)
  have hs := lat_of_same_coords (by norm_num) n.id y yr (fun i => by
    have := congrFun htv i; exact this.symm)
  set κ := dot (n.s 0) (fun c => yr c - y c) with hκ
  have hy : ∀ a, yr a = y a + κ * hN n.rows 0 a := by
    intro a
    have := hs a
    simpa [Fin.sum_univ_one, hκ] using this
  have hmain := comb_shift n y yr c0 c1 κ hy
  have hgcd := hp.1
  have hdet : 0 < gF (rowsR (setRow n.rows 1 y) 2) := by
    rw [snoc_rows, gF_snoc (by norm_num) n.id y]
    exact qform_pos n y hgcd
  have hex : existsShorter (gramM (rowsR (setRow n.rows 1 y) (1 + 1))) (dot (hN n.rows 0) (hN n.rows 0)) := by
    rw [gram_existsShorter_iff _ hdet]
    refine ⟨![c0 + c1 * κ, c1], ?_, ?_⟩
    · by_cases h1 : c1 = 0
      · refine ⟨0, ?_⟩
        have : c0 ≠ 0 := by tauto
        simp [h1, this]
      · exact ⟨1, by simpa using h1⟩
    · rw [hmain]
      simpa [ctxOf, Ctx.a, mul_assoc, mul_comm, mul_left_comm] using hlt
  exact hp.2.2.2.1 hex

/-! ## 6. Necessity -/

theorem childPass_imp_passB (n : NodeW 1 4) (bn bd : ℤ) (hbd : 0 < bd)
    (hrad : radFrac (Cq (1 + 1)) n.wit n.rows 1 n.rk = (bn : ℚ) / bd) (y : V5) (hp : ChildPass n y) :
    passB (ctxOf n bn bd) (tvec n.b y) = true := by
  have hbo : ballB (ctxOf n bn bd) (tvec n.b y) = true := by
    unfold ballB
    set yr := liftY n.r (hN n.rows 0) (tvec n.b y) with hyr
    have htv : tvec n.b yr = tvec n.b y := tvec_liftY n (tvec n.b y)
    have e1 := qform_eq n yr
    have e2 := qform_congr n htv.symm
    have h := ball_of_pass n bn bd hbd hrad y hp
    rw [e2, e1] at h
    simpa [ctxOf, Ctx.a, sq] using h
  have hg := greedy_of_pass n bn bd y hp
  have hei : ¬ eiBad (ctxOf n bn bd).b (tvec n.b y) := hp.2.2.1
  unfold passB
  simp [hp.1, hp.2.1, hei, hbo, hg]

/-! ## 7. The list-completeness checker -/

/-- The coordinates stored in a flat record (first four entries). -/
def recT (r : List ℤ) : Fin 4 → ℤ := ![r.getD 0 0, r.getD 1 0, r.getD 2 0, r.getD 3 0]

def recIs (r : List ℤ) (a b c d : ℤ) : Bool :=
  (r.getD 0 0 == a) && (r.getD 1 0 == b) && (r.getD 2 0 == c) && (r.getD 3 0 == d)

theorem recIs_eq {r : List ℤ} {a b c d : ℤ} (h : recIs r a b c d = true) : recT r = ![a, b, c, d] := by
  unfold recIs at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := h
  funext i; fin_cases i
  exacts [h0, h1, h2, h3]

def tmaxOf (c : Ctx) (i : Fin 4) : ℤ := isqrtI (c.bn * dot (c.b i) (c.b i) / c.bd)

def sliceOk (c : Ctx) (g : ℤ × List (List ℤ)) (t1 : ℤ) : Bool :=
  (rngI (tmaxOf c 2)).all fun t2 => (rngI (tmaxOf c 3)).all fun t3 =>
    !passB c ![g.1, t1, t2, t3] || g.2.any fun r => recIs r g.1 t1 t2 t3

/-- The monolithic checker (kept for the statement; the kernel runs it slice by slice, `sliceOk`). -/
def boxOk (c : Ctx) (G : List (ℤ × List (List ℤ))) : Bool :=
  (G.map Prod.fst == rngI (tmaxOf c 0)) && G.all fun g => (rngI (tmaxOf c 1)).all fun t1 => sliceOk c g t1

theorem tmax_nonneg (c : Ctx) (i : Fin 4) : 0 ≤ tmaxOf c i := by
  unfold tmaxOf isqrtI; exact Int.natCast_nonneg _

/-- **List completeness.**  If the keys are the `t0` range and every slice `(t0, t1)` of the box is accepted, every `y` with
`ChildPass n y` has its coordinate vector `b y` stored in the list. -/
theorem child_list_complete (n : NodeW 1 4) (bn bd : ℤ) (hbd : 0 < bd)
    (hrad : radFrac (Cq (1 + 1)) n.wit n.rows 1 n.rk = (bn : ℚ) / bd)
    (G : List (ℤ × List (List ℤ))) (hkeys : G.map Prod.fst = rngI (tmaxOf (ctxOf n bn bd) 0))
    (hs : ∀ g ∈ G, ∀ t1 ∈ rngI (tmaxOf (ctxOf n bn bd) 1), sliceOk (ctxOf n bn bd) g t1 = true)
    (y : V5) (hp : ChildPass n y) :
    ∃ g ∈ G, ∃ r ∈ g.2, recT r = tvec n.b y := by
  have hpass := childPass_imp_passB n bn bd hbd hrad y hp
  have hbox : ∀ i, |tvec n.b y i| ≤ tmaxOf (ctxOf n bn bd) i := fun i => by
    have hq : qform n.b y * bd < bn * (gramK n.b).det := by
      rw [det_gramK]; exact ball_of_pass n bn bd hbd hrad y hp
    have := box_covers (by norm_num) n.id y i bn bd hbd hq
    simpa [tmaxOf, ctxOf, gramK] using this
  have h0 : tvec n.b y 0 ∈ G.map Prod.fst := by
    rw [hkeys, mem_rngI (tmax_nonneg _ 0)]; exact hbox 0
  obtain ⟨g, hg, hg0⟩ := List.mem_map.1 h0
  have h1 := hs g hg (tvec n.b y 1) ((mem_rngI (tmax_nonneg _ 1)).2 (hbox 1))
  unfold sliceOk at h1
  simp only [List.all_eq_true] at h1
  have h2 := h1 (tvec n.b y 2) ((mem_rngI (tmax_nonneg _ 2)).2 (hbox 2))
  simp only [List.all_eq_true] at h2
  have h3 := h2 (tvec n.b y 3) ((mem_rngI (tmax_nonneg _ 3)).2 (hbox 3))
  have ht : (![g.1, tvec n.b y 1, tvec n.b y 2, tvec n.b y 3] : Fin 4 → ℤ) = tvec n.b y := by
    funext i; fin_cases i <;> simp [hg0]
  rw [ht] at h3
  simp only [Bool.or_eq_true, Bool.not_eq_true', List.any_eq_true] at h3
  rcases h3 with h | ⟨r, hr, hrt⟩
  · rw [hpass] at h; exact absurd h (by simp)
  · exact ⟨g, hg, r, hr, by rw [recIs_eq hrt, ht]⟩

end L5S4
end LRSpectrumFull

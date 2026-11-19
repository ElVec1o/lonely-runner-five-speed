/-
# L5S4.GD3O304 : `StreamHyp'.t3` for rep #304 with NO hypothesis: flat leaf checker on the kind-1/2 pieces, `critOk` on the kind-0 pieces, class-table cover for the local table (S4O)

No `sorry`, no `native_decide`, no new axiom.  Not registered in any aggregator.
-/
import LRSpectrumFull.L5S4.GD3O304Rc0p0
import LRSpectrumFull.L5S4.GD3O304Rc0p1
import LRSpectrumFull.L5S4.GD3O304Rc0p2
import LRSpectrumFull.L5S4.GD3O304Rc0p3
import LRSpectrumFull.L5S4.GD3O304Rc0p4
import LRSpectrumFull.L5S4.GD3O304Rc0p5
import LRSpectrumFull.L5S4.GD3O304Rc0p6
import LRSpectrumFull.L5S4.GD3O304Rc1
import LRSpectrumFull.L5S4.GD3O304Rc2
import LRSpectrumFull.L5S4.GD3O304Rc3
import LRSpectrumFull.L5S4.GD3O304Rc4
import LRSpectrumFull.L5S4.GD3O304Rc5
import LRSpectrumFull.L5S4.GD3O304Rc6
import LRSpectrumFull.L5S4.GD3O304Rc7
import LRSpectrumFull.L5S4.GD3O304Rc8
import LRSpectrumFull.L5S4.GD3O304Rc9
import LRSpectrumFull.L5S4.GD3O304Rc10
import LRSpectrumFull.L5S4.GD3O304Rc11
import LRSpectrumFull.L5S4.GD3O304Rc12
import LRSpectrumFull.L5S4.GD3O304Rc13
import LRSpectrumFull.L5S4.GD3O304Rc14
import LRSpectrumFull.L5S4.GD3O304Rc15
import LRSpectrumFull.L5S4.GD3O304Rc16
import LRSpectrumFull.L5S4.GD3O304Rc17
import LRSpectrumFull.L5S4.GD3O304Rc18
import LRSpectrumFull.L5S4.GD3O304Rc19
import LRSpectrumFull.L5S4.GD3O304Rc20
import LRSpectrumFull.L5S4.GD3O304Rc21
import LRSpectrumFull.L5S4.GD3O304Rc22
import LRSpectrumFull.L5S4.GD3O304Rc23
import LRSpectrumFull.L5S4.GD3O304Rc24
import LRSpectrumFull.L5S4.GD3O304Rc25
import LRSpectrumFull.L5S4.GD3O304Rc26
import LRSpectrumFull.L5S4.GD3O304Rc27
import LRSpectrumFull.L5S4.GD3O304Rc28
import LRSpectrumFull.L5S4.GD3O304Rc29
import LRSpectrumFull.L5S4.GD3O304Rc30
import LRSpectrumFull.L5S4.GD3O304Rc31
import LRSpectrumFull.L5S4.GD3O304Rc32
import LRSpectrumFull.L5S4.GD3O304Rc33
import LRSpectrumFull.L5S4.GD3O304Rc34
import LRSpectrumFull.L5S4.GD3O304Rc35
import LRSpectrumFull.L5S4.GD3O304Rc36
import LRSpectrumFull.L5S4.GD3O304Rc37
import LRSpectrumFull.L5S4.GD3O304Rc38
import LRSpectrumFull.L5S4.GD3O304Rc39
import LRSpectrumFull.L5S4.GD3O304Rc40
import LRSpectrumFull.L5S4.GD3O304Rc41
import LRSpectrumFull.L5S4.GD3O304Rc42
import LRSpectrumFull.L5S4.GD3O304Rc43
import LRSpectrumFull.L5S4.GD3O304Rc44
import LRSpectrumFull.L5S4.GD3O304Rc45
import LRSpectrumFull.L5S4.GD3O304Rc46
import LRSpectrumFull.L5S4.GD3O304Rc47
import LRSpectrumFull.L5S4.GD3O304Rc48
import LRSpectrumFull.L5S4.GD3O304Rc49
import LRSpectrumFull.L5S4.GD3O304Rc50
import LRSpectrumFull.L5S4.GD3O304Rc51
import LRSpectrumFull.L5S4.GD3O304Rc52
import LRSpectrumFull.L5S4.GD3O304Rc53
import LRSpectrumFull.L5S4.GD3O304Rc54
import LRSpectrumFull.L5S4.GD3O304Rc55
import LRSpectrumFull.L5S4.GD3O304Rc56
import LRSpectrumFull.L5S4.GD3O304Rc57
import LRSpectrumFull.L5S4.GD3O304Rc58
import LRSpectrumFull.L5S4.GD3O304Rc59
import LRSpectrumFull.L5S4.GD3O304Rc60
import LRSpectrumFull.L5S4.GD3O304Rc61
import LRSpectrumFull.L5S4.GD3O304X
import LRSpectrumFull.L5S4.GD3F2N304
import LRSpectrumFull.L5S4.GD3O304T
import LRSpectrumFull.L5S4.GD3N304Z

set_option maxRecDepth 1000000
set_option maxHeartbeats 0

namespace LRSpectrumFull
namespace L5S4
namespace N304
open Matrix Finset LRSpectrumFull.L5S3

def fm (l : List ℕ) : List LeafRec := l.map fun N => recOf (dg N)

def tabO : List T4Rec := (List.range nT).map (t4At (dg TT) ST)
def Crep : Certificate := ⟨[], [], [], [], tabO, []⟩

theorem flatOk (bl : List ℕ) (h : (bl.all fun N => leafOkF (dg NN) (dg N) && t4F (dg TT) ST nT (dg N)) = true) :
    (∀ r ∈ fm bl, leafOk nK r = true) ∧ T4Cover Crep (fm bl) := by
  have h' := List.all_eq_true.1 h
  refine ⟨?_, ?_⟩
  · intro r hr
    obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hr
    have := h' N hN
    simp only [Bool.and_eq_true] at this
    exact leafOkF_sound nK (dg NN) (dg N) ag this.1
  · intro r hr hk0 hk1
    obtain ⟨N, hN, rfl⟩ := List.mem_map.1 hr
    have := h' N hN
    simp only [Bool.and_eq_true] at this
    exact t4F_sound (dg TT) ST nT (dg N) this.2 hk0 hk1

theorem critPieceOk (l : List LeafRec) (h1 : (l.all fun r => leafOk nK r) = true) (h2 : (l.all fun r => r.kind == 0) = true) :
    (∀ r ∈ l, leafOk nK r = true) ∧ T4Cover Crep l := by
  refine ⟨fun r hr => List.all_eq_true.1 h1 r hr, ?_⟩
  intro r hr hk0 _
  exact absurd (beq_iff_eq.1 (List.all_eq_true.1 h2 r hr)) hk0

theorem app2 {l1 l2 : List LeafRec} (a : (∀ r ∈ l1, leafOk nK r = true) ∧ T4Cover Crep l1)
    (b : (∀ r ∈ l2, leafOk nK r = true) ∧ T4Cover Crep l2) : (∀ r ∈ l1 ++ l2, leafOk nK r = true) ∧ T4Cover Crep (l1 ++ l2) := by
  refine ⟨fun r hr => ?_, fun r hr hk0 hk1 => ?_⟩
  · rcases List.mem_append.1 hr with h | h
    · exact a.1 r h
    · exact b.1 r h
  · rcases List.mem_append.1 hr with h | h
    · exact a.2 r h hk0 hk1
    · exact b.2 r h hk0 hk1

def recsO : List LeafRec := (fm blobsO_c0p0) ++ (recsX_0) ++ (fm blobsO_c0p1) ++ (recsX_1) ++ (fm blobsO_c0p2) ++ (recsX_2) ++ (fm blobsO_c0p3) ++ (recsX_3) ++ (fm blobsO_c0p4) ++ (recsX_4) ++ (fm blobsO_c0p5) ++ (recsX_5) ++ (fm blobsO_c0p6) ++ (fm blobsO_c1) ++ (fm blobsO_c2) ++ (fm blobsO_c3) ++ (fm blobsO_c4) ++ (fm blobsO_c5) ++ (fm blobsO_c6) ++ (fm blobsO_c7) ++ (fm blobsO_c8) ++ (fm blobsO_c9) ++ (fm blobsO_c10) ++ (fm blobsO_c11) ++ (fm blobsO_c12) ++ (fm blobsO_c13) ++ (fm blobsO_c14) ++ (fm blobsO_c15) ++ (fm blobsO_c16) ++ (fm blobsO_c17) ++ (fm blobsO_c18) ++ (fm blobsO_c19) ++ (fm blobsO_c20) ++ (fm blobsO_c21) ++ (fm blobsO_c22) ++ (fm blobsO_c23) ++ (fm blobsO_c24) ++ (fm blobsO_c25) ++ (fm blobsO_c26) ++ (fm blobsO_c27) ++ (fm blobsO_c28) ++ (fm blobsO_c29) ++ (fm blobsO_c30) ++ (fm blobsO_c31) ++ (fm blobsO_c32) ++ (fm blobsO_c33) ++ (fm blobsO_c34) ++ (fm blobsO_c35) ++ (fm blobsO_c36) ++ (fm blobsO_c37) ++ (fm blobsO_c38) ++ (fm blobsO_c39) ++ (fm blobsO_c40) ++ (fm blobsO_c41) ++ (fm blobsO_c42) ++ (fm blobsO_c43) ++ (fm blobsO_c44) ++ (fm blobsO_c45) ++ (fm blobsO_c46) ++ (fm blobsO_c47) ++ (fm blobsO_c48) ++ (fm blobsO_c49) ++ (fm blobsO_c50) ++ (fm blobsO_c51) ++ (fm blobsO_c52) ++ (fm blobsO_c53) ++ (fm blobsO_c54) ++ (fm blobsO_c55) ++ (fm blobsO_c56) ++ (fm blobsO_c57) ++ (fm blobsO_c58) ++ (fm blobsO_c59) ++ (fm blobsO_c60) ++ (fm blobsO_c61)

theorem piecesO : (∀ r ∈ recsO, leafOk nK r = true) ∧ T4Cover Crep recsO := (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (app2 (flatOk _ okO_c0p0) (critPieceOk _ okX_0 kindX_0)) (flatOk _ okO_c0p1)) (critPieceOk _ okX_1 kindX_1)) (flatOk _ okO_c0p2)) (critPieceOk _ okX_2 kindX_2)) (flatOk _ okO_c0p3)) (critPieceOk _ okX_3 kindX_3)) (flatOk _ okO_c0p4)) (critPieceOk _ okX_4 kindX_4)) (flatOk _ okO_c0p5)) (critPieceOk _ okX_5 kindX_5)) (flatOk _ okO_c0p6)) (flatOk _ okO_c1)) (flatOk _ okO_c2)) (flatOk _ okO_c3)) (flatOk _ okO_c4)) (flatOk _ okO_c5)) (flatOk _ okO_c6)) (flatOk _ okO_c7)) (flatOk _ okO_c8)) (flatOk _ okO_c9)) (flatOk _ okO_c10)) (flatOk _ okO_c11)) (flatOk _ okO_c12)) (flatOk _ okO_c13)) (flatOk _ okO_c14)) (flatOk _ okO_c15)) (flatOk _ okO_c16)) (flatOk _ okO_c17)) (flatOk _ okO_c18)) (flatOk _ okO_c19)) (flatOk _ okO_c20)) (flatOk _ okO_c21)) (flatOk _ okO_c22)) (flatOk _ okO_c23)) (flatOk _ okO_c24)) (flatOk _ okO_c25)) (flatOk _ okO_c26)) (flatOk _ okO_c27)) (flatOk _ okO_c28)) (flatOk _ okO_c29)) (flatOk _ okO_c30)) (flatOk _ okO_c31)) (flatOk _ okO_c32)) (flatOk _ okO_c33)) (flatOk _ okO_c34)) (flatOk _ okO_c35)) (flatOk _ okO_c36)) (flatOk _ okO_c37)) (flatOk _ okO_c38)) (flatOk _ okO_c39)) (flatOk _ okO_c40)) (flatOk _ okO_c41)) (flatOk _ okO_c42)) (flatOk _ okO_c43)) (flatOk _ okO_c44)) (flatOk _ okO_c45)) (flatOk _ okO_c46)) (flatOk _ okO_c47)) (flatOk _ okO_c48)) (flatOk _ okO_c49)) (flatOk _ okO_c50)) (flatOk _ okO_c51)) (flatOk _ okO_c52)) (flatOk _ okO_c53)) (flatOk _ okO_c54)) (flatOk _ okO_c55)) (flatOk _ okO_c56)) (flatOk _ okO_c57)) (flatOk _ okO_c58)) (flatOk _ okO_c59)) (flatOk _ okO_c60)) (flatOk _ okO_c61))

theorem alignO : storedOf cks = recsO.map LeafRec.t := by decide +kernel

theorem recsO_ok : ∀ r ∈ recsO, leafOk nK r = true := piecesO.1

theorem t4coverO : T4Cover Crep recsO := piecesO.2

/-- `StreamHyp'.t3` for rep #304 with NO hypothesis, for the local certificate `Crep`. -/
theorem t3_nodeU :
    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧
      n3.rows = setRow nK.rows 2 y' ∧ LeafRelW Crep n3 :=
  fun y hy => t3_leaves Crep nK bn bd (by norm_num [bd]) hrad cks (by rw [fc_eq]; exact cov) (by rw [fc_eq]; exact allok)
    recsO alignO recsO_ok t4coverO y hy

/-- Lifting to any certificate whose table registers every local class (same rows, ranges covered). -/
theorem t3_nodeU_of (C : Certificate) (hsub : LocRegistered C tabO) :
    ∀ y : V5, ChildPass nK y → ∃ (y' : V5) (n3 : LeafW), (∀ i, dot (nK.b i) y' = dot (nK.b i) y) ∧
      n3.rows = setRow nK.rows 2 y' ∧ LeafRelW C n3 := by
  intro y hy
  obtain ⟨y', n3, h1, h2, h3⟩ := t3_nodeU y hy
  exact ⟨y', n3, h1, h2, leafRelW_of_registered hsub h3⟩

#print axioms t3_nodeU
#print axioms t3_nodeU_of


end N304
end L5S4
end LRSpectrumFull

/-
# L5S4.LinRQSG21 : node S group 21 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC672
import LRSpectrumFull.L5S4.LinRQSC673
import LRSpectrumFull.L5S4.LinRQSC674
import LRSpectrumFull.L5S4.LinRQSC675
import LRSpectrumFull.L5S4.LinRQSC676
import LRSpectrumFull.L5S4.LinRQSC677
import LRSpectrumFull.L5S4.LinRQSC678
import LRSpectrumFull.L5S4.LinRQSC679
import LRSpectrumFull.L5S4.LinRQSC680
import LRSpectrumFull.L5S4.LinRQSC681
import LRSpectrumFull.L5S4.LinRQSC682
import LRSpectrumFull.L5S4.LinRQSC683
import LRSpectrumFull.L5S4.LinRQSC684
import LRSpectrumFull.L5S4.LinRQSC685
import LRSpectrumFull.L5S4.LinRQSC686
import LRSpectrumFull.L5S4.LinRQSC687
import LRSpectrumFull.L5S4.LinRQSC688
import LRSpectrumFull.L5S4.LinRQSC689
import LRSpectrumFull.L5S4.LinRQSC690
import LRSpectrumFull.L5S4.LinRQSC691
import LRSpectrumFull.L5S4.LinRQSC692
import LRSpectrumFull.L5S4.LinRQSC693
import LRSpectrumFull.L5S4.LinRQSC694
import LRSpectrumFull.L5S4.LinRQSC695
import LRSpectrumFull.L5S4.LinRQSC696
import LRSpectrumFull.L5S4.LinRQSC697
import LRSpectrumFull.L5S4.LinRQSC698
import LRSpectrumFull.L5S4.LinRQSC699
import LRSpectrumFull.L5S4.LinRQSC700
import LRSpectrumFull.L5S4.LinRQSC701
import LRSpectrumFull.L5S4.LinRQSC702
import LRSpectrumFull.L5S4.LinRQSC703

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG21

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC672.blobs ++ (LinRQSC673.blobs ++ (LinRQSC674.blobs ++ (LinRQSC675.blobs ++ (LinRQSC676.blobs ++ (LinRQSC677.blobs ++ (LinRQSC678.blobs ++ (LinRQSC679.blobs ++ (LinRQSC680.blobs ++ (LinRQSC681.blobs ++ (LinRQSC682.blobs ++ (LinRQSC683.blobs ++ (LinRQSC684.blobs ++ (LinRQSC685.blobs ++ (LinRQSC686.blobs ++ (LinRQSC687.blobs ++ (LinRQSC688.blobs ++ (LinRQSC689.blobs ++ (LinRQSC690.blobs ++ (LinRQSC691.blobs ++ (LinRQSC692.blobs ++ (LinRQSC693.blobs ++ (LinRQSC694.blobs ++ (LinRQSC695.blobs ++ (LinRQSC696.blobs ++ (LinRQSC697.blobs ++ (LinRQSC698.blobs ++ (LinRQSC699.blobs ++ (LinRQSC700.blobs ++ (LinRQSC701.blobs ++ (LinRQSC702.blobs ++ (LinRQSC703.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC672.ok (chunksR_ok_append LinRQSC673.ok (chunksR_ok_append LinRQSC674.ok (chunksR_ok_append LinRQSC675.ok (chunksR_ok_append LinRQSC676.ok (chunksR_ok_append LinRQSC677.ok (chunksR_ok_append LinRQSC678.ok (chunksR_ok_append LinRQSC679.ok (chunksR_ok_append LinRQSC680.ok (chunksR_ok_append LinRQSC681.ok (chunksR_ok_append LinRQSC682.ok (chunksR_ok_append LinRQSC683.ok (chunksR_ok_append LinRQSC684.ok (chunksR_ok_append LinRQSC685.ok (chunksR_ok_append LinRQSC686.ok (chunksR_ok_append LinRQSC687.ok (chunksR_ok_append LinRQSC688.ok (chunksR_ok_append LinRQSC689.ok (chunksR_ok_append LinRQSC690.ok (chunksR_ok_append LinRQSC691.ok (chunksR_ok_append LinRQSC692.ok (chunksR_ok_append LinRQSC693.ok (chunksR_ok_append LinRQSC694.ok (chunksR_ok_append LinRQSC695.ok (chunksR_ok_append LinRQSC696.ok (chunksR_ok_append LinRQSC697.ok (chunksR_ok_append LinRQSC698.ok (chunksR_ok_append LinRQSC699.ok (chunksR_ok_append LinRQSC700.ok (chunksR_ok_append LinRQSC701.ok (chunksR_ok_append LinRQSC702.ok (LinRQSC703.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG21
end L5S4
end LRSpectrumFull

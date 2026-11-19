/-
# L5S4.LinRQSG23 : node S group 23 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC736
import LRSpectrumFull.L5S4.LinRQSC737
import LRSpectrumFull.L5S4.LinRQSC738
import LRSpectrumFull.L5S4.LinRQSC739
import LRSpectrumFull.L5S4.LinRQSC740
import LRSpectrumFull.L5S4.LinRQSC741
import LRSpectrumFull.L5S4.LinRQSC742
import LRSpectrumFull.L5S4.LinRQSC743
import LRSpectrumFull.L5S4.LinRQSC744
import LRSpectrumFull.L5S4.LinRQSC745
import LRSpectrumFull.L5S4.LinRQSC746
import LRSpectrumFull.L5S4.LinRQSC747
import LRSpectrumFull.L5S4.LinRQSC748
import LRSpectrumFull.L5S4.LinRQSC749
import LRSpectrumFull.L5S4.LinRQSC750
import LRSpectrumFull.L5S4.LinRQSC751
import LRSpectrumFull.L5S4.LinRQSC752
import LRSpectrumFull.L5S4.LinRQSC753
import LRSpectrumFull.L5S4.LinRQSC754
import LRSpectrumFull.L5S4.LinRQSC755
import LRSpectrumFull.L5S4.LinRQSC756
import LRSpectrumFull.L5S4.LinRQSC757
import LRSpectrumFull.L5S4.LinRQSC758
import LRSpectrumFull.L5S4.LinRQSC759
import LRSpectrumFull.L5S4.LinRQSC760
import LRSpectrumFull.L5S4.LinRQSC761
import LRSpectrumFull.L5S4.LinRQSC762
import LRSpectrumFull.L5S4.LinRQSC763
import LRSpectrumFull.L5S4.LinRQSC764
import LRSpectrumFull.L5S4.LinRQSC765
import LRSpectrumFull.L5S4.LinRQSC766
import LRSpectrumFull.L5S4.LinRQSC767

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG23

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC736.blobs ++ (LinRQSC737.blobs ++ (LinRQSC738.blobs ++ (LinRQSC739.blobs ++ (LinRQSC740.blobs ++ (LinRQSC741.blobs ++ (LinRQSC742.blobs ++ (LinRQSC743.blobs ++ (LinRQSC744.blobs ++ (LinRQSC745.blobs ++ (LinRQSC746.blobs ++ (LinRQSC747.blobs ++ (LinRQSC748.blobs ++ (LinRQSC749.blobs ++ (LinRQSC750.blobs ++ (LinRQSC751.blobs ++ (LinRQSC752.blobs ++ (LinRQSC753.blobs ++ (LinRQSC754.blobs ++ (LinRQSC755.blobs ++ (LinRQSC756.blobs ++ (LinRQSC757.blobs ++ (LinRQSC758.blobs ++ (LinRQSC759.blobs ++ (LinRQSC760.blobs ++ (LinRQSC761.blobs ++ (LinRQSC762.blobs ++ (LinRQSC763.blobs ++ (LinRQSC764.blobs ++ (LinRQSC765.blobs ++ (LinRQSC766.blobs ++ (LinRQSC767.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC736.ok (chunksR_ok_append LinRQSC737.ok (chunksR_ok_append LinRQSC738.ok (chunksR_ok_append LinRQSC739.ok (chunksR_ok_append LinRQSC740.ok (chunksR_ok_append LinRQSC741.ok (chunksR_ok_append LinRQSC742.ok (chunksR_ok_append LinRQSC743.ok (chunksR_ok_append LinRQSC744.ok (chunksR_ok_append LinRQSC745.ok (chunksR_ok_append LinRQSC746.ok (chunksR_ok_append LinRQSC747.ok (chunksR_ok_append LinRQSC748.ok (chunksR_ok_append LinRQSC749.ok (chunksR_ok_append LinRQSC750.ok (chunksR_ok_append LinRQSC751.ok (chunksR_ok_append LinRQSC752.ok (chunksR_ok_append LinRQSC753.ok (chunksR_ok_append LinRQSC754.ok (chunksR_ok_append LinRQSC755.ok (chunksR_ok_append LinRQSC756.ok (chunksR_ok_append LinRQSC757.ok (chunksR_ok_append LinRQSC758.ok (chunksR_ok_append LinRQSC759.ok (chunksR_ok_append LinRQSC760.ok (chunksR_ok_append LinRQSC761.ok (chunksR_ok_append LinRQSC762.ok (chunksR_ok_append LinRQSC763.ok (chunksR_ok_append LinRQSC764.ok (chunksR_ok_append LinRQSC765.ok (chunksR_ok_append LinRQSC766.ok (LinRQSC767.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG23
end L5S4
end LRSpectrumFull

/-
# L5S4.LinRQSG22 : node S group 22 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC704
import LRSpectrumFull.L5S4.LinRQSC705
import LRSpectrumFull.L5S4.LinRQSC706
import LRSpectrumFull.L5S4.LinRQSC707
import LRSpectrumFull.L5S4.LinRQSC708
import LRSpectrumFull.L5S4.LinRQSC709
import LRSpectrumFull.L5S4.LinRQSC710
import LRSpectrumFull.L5S4.LinRQSC711
import LRSpectrumFull.L5S4.LinRQSC712
import LRSpectrumFull.L5S4.LinRQSC713
import LRSpectrumFull.L5S4.LinRQSC714
import LRSpectrumFull.L5S4.LinRQSC715
import LRSpectrumFull.L5S4.LinRQSC716
import LRSpectrumFull.L5S4.LinRQSC717
import LRSpectrumFull.L5S4.LinRQSC718
import LRSpectrumFull.L5S4.LinRQSC719
import LRSpectrumFull.L5S4.LinRQSC720
import LRSpectrumFull.L5S4.LinRQSC721
import LRSpectrumFull.L5S4.LinRQSC722
import LRSpectrumFull.L5S4.LinRQSC723
import LRSpectrumFull.L5S4.LinRQSC724
import LRSpectrumFull.L5S4.LinRQSC725
import LRSpectrumFull.L5S4.LinRQSC726
import LRSpectrumFull.L5S4.LinRQSC727
import LRSpectrumFull.L5S4.LinRQSC728
import LRSpectrumFull.L5S4.LinRQSC729
import LRSpectrumFull.L5S4.LinRQSC730
import LRSpectrumFull.L5S4.LinRQSC731
import LRSpectrumFull.L5S4.LinRQSC732
import LRSpectrumFull.L5S4.LinRQSC733
import LRSpectrumFull.L5S4.LinRQSC734
import LRSpectrumFull.L5S4.LinRQSC735

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG22

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC704.blobs ++ (LinRQSC705.blobs ++ (LinRQSC706.blobs ++ (LinRQSC707.blobs ++ (LinRQSC708.blobs ++ (LinRQSC709.blobs ++ (LinRQSC710.blobs ++ (LinRQSC711.blobs ++ (LinRQSC712.blobs ++ (LinRQSC713.blobs ++ (LinRQSC714.blobs ++ (LinRQSC715.blobs ++ (LinRQSC716.blobs ++ (LinRQSC717.blobs ++ (LinRQSC718.blobs ++ (LinRQSC719.blobs ++ (LinRQSC720.blobs ++ (LinRQSC721.blobs ++ (LinRQSC722.blobs ++ (LinRQSC723.blobs ++ (LinRQSC724.blobs ++ (LinRQSC725.blobs ++ (LinRQSC726.blobs ++ (LinRQSC727.blobs ++ (LinRQSC728.blobs ++ (LinRQSC729.blobs ++ (LinRQSC730.blobs ++ (LinRQSC731.blobs ++ (LinRQSC732.blobs ++ (LinRQSC733.blobs ++ (LinRQSC734.blobs ++ (LinRQSC735.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC704.ok (chunksR_ok_append LinRQSC705.ok (chunksR_ok_append LinRQSC706.ok (chunksR_ok_append LinRQSC707.ok (chunksR_ok_append LinRQSC708.ok (chunksR_ok_append LinRQSC709.ok (chunksR_ok_append LinRQSC710.ok (chunksR_ok_append LinRQSC711.ok (chunksR_ok_append LinRQSC712.ok (chunksR_ok_append LinRQSC713.ok (chunksR_ok_append LinRQSC714.ok (chunksR_ok_append LinRQSC715.ok (chunksR_ok_append LinRQSC716.ok (chunksR_ok_append LinRQSC717.ok (chunksR_ok_append LinRQSC718.ok (chunksR_ok_append LinRQSC719.ok (chunksR_ok_append LinRQSC720.ok (chunksR_ok_append LinRQSC721.ok (chunksR_ok_append LinRQSC722.ok (chunksR_ok_append LinRQSC723.ok (chunksR_ok_append LinRQSC724.ok (chunksR_ok_append LinRQSC725.ok (chunksR_ok_append LinRQSC726.ok (chunksR_ok_append LinRQSC727.ok (chunksR_ok_append LinRQSC728.ok (chunksR_ok_append LinRQSC729.ok (chunksR_ok_append LinRQSC730.ok (chunksR_ok_append LinRQSC731.ok (chunksR_ok_append LinRQSC732.ok (chunksR_ok_append LinRQSC733.ok (chunksR_ok_append LinRQSC734.ok (LinRQSC735.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG22
end L5S4
end LRSpectrumFull

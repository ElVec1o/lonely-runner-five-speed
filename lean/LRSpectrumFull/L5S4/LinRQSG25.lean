/-
# L5S4.LinRQSG25 : node S group 25 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC800
import LRSpectrumFull.L5S4.LinRQSC801
import LRSpectrumFull.L5S4.LinRQSC802
import LRSpectrumFull.L5S4.LinRQSC803
import LRSpectrumFull.L5S4.LinRQSC804
import LRSpectrumFull.L5S4.LinRQSC805
import LRSpectrumFull.L5S4.LinRQSC806
import LRSpectrumFull.L5S4.LinRQSC807
import LRSpectrumFull.L5S4.LinRQSC808
import LRSpectrumFull.L5S4.LinRQSC809
import LRSpectrumFull.L5S4.LinRQSC810
import LRSpectrumFull.L5S4.LinRQSC811
import LRSpectrumFull.L5S4.LinRQSC812
import LRSpectrumFull.L5S4.LinRQSC813
import LRSpectrumFull.L5S4.LinRQSC814
import LRSpectrumFull.L5S4.LinRQSC815
import LRSpectrumFull.L5S4.LinRQSC816
import LRSpectrumFull.L5S4.LinRQSC817
import LRSpectrumFull.L5S4.LinRQSC818
import LRSpectrumFull.L5S4.LinRQSC819
import LRSpectrumFull.L5S4.LinRQSC820
import LRSpectrumFull.L5S4.LinRQSC821
import LRSpectrumFull.L5S4.LinRQSC822
import LRSpectrumFull.L5S4.LinRQSC823
import LRSpectrumFull.L5S4.LinRQSC824
import LRSpectrumFull.L5S4.LinRQSC825
import LRSpectrumFull.L5S4.LinRQSC826
import LRSpectrumFull.L5S4.LinRQSC827
import LRSpectrumFull.L5S4.LinRQSC828
import LRSpectrumFull.L5S4.LinRQSC829
import LRSpectrumFull.L5S4.LinRQSC830
import LRSpectrumFull.L5S4.LinRQSC831

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG25

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC800.blobs ++ (LinRQSC801.blobs ++ (LinRQSC802.blobs ++ (LinRQSC803.blobs ++ (LinRQSC804.blobs ++ (LinRQSC805.blobs ++ (LinRQSC806.blobs ++ (LinRQSC807.blobs ++ (LinRQSC808.blobs ++ (LinRQSC809.blobs ++ (LinRQSC810.blobs ++ (LinRQSC811.blobs ++ (LinRQSC812.blobs ++ (LinRQSC813.blobs ++ (LinRQSC814.blobs ++ (LinRQSC815.blobs ++ (LinRQSC816.blobs ++ (LinRQSC817.blobs ++ (LinRQSC818.blobs ++ (LinRQSC819.blobs ++ (LinRQSC820.blobs ++ (LinRQSC821.blobs ++ (LinRQSC822.blobs ++ (LinRQSC823.blobs ++ (LinRQSC824.blobs ++ (LinRQSC825.blobs ++ (LinRQSC826.blobs ++ (LinRQSC827.blobs ++ (LinRQSC828.blobs ++ (LinRQSC829.blobs ++ (LinRQSC830.blobs ++ (LinRQSC831.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC800.ok (chunksR_ok_append LinRQSC801.ok (chunksR_ok_append LinRQSC802.ok (chunksR_ok_append LinRQSC803.ok (chunksR_ok_append LinRQSC804.ok (chunksR_ok_append LinRQSC805.ok (chunksR_ok_append LinRQSC806.ok (chunksR_ok_append LinRQSC807.ok (chunksR_ok_append LinRQSC808.ok (chunksR_ok_append LinRQSC809.ok (chunksR_ok_append LinRQSC810.ok (chunksR_ok_append LinRQSC811.ok (chunksR_ok_append LinRQSC812.ok (chunksR_ok_append LinRQSC813.ok (chunksR_ok_append LinRQSC814.ok (chunksR_ok_append LinRQSC815.ok (chunksR_ok_append LinRQSC816.ok (chunksR_ok_append LinRQSC817.ok (chunksR_ok_append LinRQSC818.ok (chunksR_ok_append LinRQSC819.ok (chunksR_ok_append LinRQSC820.ok (chunksR_ok_append LinRQSC821.ok (chunksR_ok_append LinRQSC822.ok (chunksR_ok_append LinRQSC823.ok (chunksR_ok_append LinRQSC824.ok (chunksR_ok_append LinRQSC825.ok (chunksR_ok_append LinRQSC826.ok (chunksR_ok_append LinRQSC827.ok (chunksR_ok_append LinRQSC828.ok (chunksR_ok_append LinRQSC829.ok (chunksR_ok_append LinRQSC830.ok (LinRQSC831.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG25
end L5S4
end LRSpectrumFull

/-
# L5S4.LinRQSG7 : node S group 7 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC224
import LRSpectrumFull.L5S4.LinRQSC225
import LRSpectrumFull.L5S4.LinRQSC226
import LRSpectrumFull.L5S4.LinRQSC227
import LRSpectrumFull.L5S4.LinRQSC228
import LRSpectrumFull.L5S4.LinRQSC229
import LRSpectrumFull.L5S4.LinRQSC230
import LRSpectrumFull.L5S4.LinRQSC231
import LRSpectrumFull.L5S4.LinRQSC232
import LRSpectrumFull.L5S4.LinRQSC233
import LRSpectrumFull.L5S4.LinRQSC234
import LRSpectrumFull.L5S4.LinRQSC235
import LRSpectrumFull.L5S4.LinRQSC236
import LRSpectrumFull.L5S4.LinRQSC237
import LRSpectrumFull.L5S4.LinRQSC238
import LRSpectrumFull.L5S4.LinRQSC239
import LRSpectrumFull.L5S4.LinRQSC240
import LRSpectrumFull.L5S4.LinRQSC241
import LRSpectrumFull.L5S4.LinRQSC242
import LRSpectrumFull.L5S4.LinRQSC243
import LRSpectrumFull.L5S4.LinRQSC244
import LRSpectrumFull.L5S4.LinRQSC245
import LRSpectrumFull.L5S4.LinRQSC246
import LRSpectrumFull.L5S4.LinRQSC247
import LRSpectrumFull.L5S4.LinRQSC248
import LRSpectrumFull.L5S4.LinRQSC249
import LRSpectrumFull.L5S4.LinRQSC250
import LRSpectrumFull.L5S4.LinRQSC251
import LRSpectrumFull.L5S4.LinRQSC252
import LRSpectrumFull.L5S4.LinRQSC253
import LRSpectrumFull.L5S4.LinRQSC254
import LRSpectrumFull.L5S4.LinRQSC255

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG7

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC224.blobs ++ (LinRQSC225.blobs ++ (LinRQSC226.blobs ++ (LinRQSC227.blobs ++ (LinRQSC228.blobs ++ (LinRQSC229.blobs ++ (LinRQSC230.blobs ++ (LinRQSC231.blobs ++ (LinRQSC232.blobs ++ (LinRQSC233.blobs ++ (LinRQSC234.blobs ++ (LinRQSC235.blobs ++ (LinRQSC236.blobs ++ (LinRQSC237.blobs ++ (LinRQSC238.blobs ++ (LinRQSC239.blobs ++ (LinRQSC240.blobs ++ (LinRQSC241.blobs ++ (LinRQSC242.blobs ++ (LinRQSC243.blobs ++ (LinRQSC244.blobs ++ (LinRQSC245.blobs ++ (LinRQSC246.blobs ++ (LinRQSC247.blobs ++ (LinRQSC248.blobs ++ (LinRQSC249.blobs ++ (LinRQSC250.blobs ++ (LinRQSC251.blobs ++ (LinRQSC252.blobs ++ (LinRQSC253.blobs ++ (LinRQSC254.blobs ++ (LinRQSC255.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC224.ok (chunksR_ok_append LinRQSC225.ok (chunksR_ok_append LinRQSC226.ok (chunksR_ok_append LinRQSC227.ok (chunksR_ok_append LinRQSC228.ok (chunksR_ok_append LinRQSC229.ok (chunksR_ok_append LinRQSC230.ok (chunksR_ok_append LinRQSC231.ok (chunksR_ok_append LinRQSC232.ok (chunksR_ok_append LinRQSC233.ok (chunksR_ok_append LinRQSC234.ok (chunksR_ok_append LinRQSC235.ok (chunksR_ok_append LinRQSC236.ok (chunksR_ok_append LinRQSC237.ok (chunksR_ok_append LinRQSC238.ok (chunksR_ok_append LinRQSC239.ok (chunksR_ok_append LinRQSC240.ok (chunksR_ok_append LinRQSC241.ok (chunksR_ok_append LinRQSC242.ok (chunksR_ok_append LinRQSC243.ok (chunksR_ok_append LinRQSC244.ok (chunksR_ok_append LinRQSC245.ok (chunksR_ok_append LinRQSC246.ok (chunksR_ok_append LinRQSC247.ok (chunksR_ok_append LinRQSC248.ok (chunksR_ok_append LinRQSC249.ok (chunksR_ok_append LinRQSC250.ok (chunksR_ok_append LinRQSC251.ok (chunksR_ok_append LinRQSC252.ok (chunksR_ok_append LinRQSC253.ok (chunksR_ok_append LinRQSC254.ok (LinRQSC255.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG7
end L5S4
end LRSpectrumFull

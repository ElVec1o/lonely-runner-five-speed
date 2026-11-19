/-
# L5S4.LinRQSG15 : node S group 15 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC480
import LRSpectrumFull.L5S4.LinRQSC481
import LRSpectrumFull.L5S4.LinRQSC482
import LRSpectrumFull.L5S4.LinRQSC483
import LRSpectrumFull.L5S4.LinRQSC484
import LRSpectrumFull.L5S4.LinRQSC485
import LRSpectrumFull.L5S4.LinRQSC486
import LRSpectrumFull.L5S4.LinRQSC487
import LRSpectrumFull.L5S4.LinRQSC488
import LRSpectrumFull.L5S4.LinRQSC489
import LRSpectrumFull.L5S4.LinRQSC490
import LRSpectrumFull.L5S4.LinRQSC491
import LRSpectrumFull.L5S4.LinRQSC492
import LRSpectrumFull.L5S4.LinRQSC493
import LRSpectrumFull.L5S4.LinRQSC494
import LRSpectrumFull.L5S4.LinRQSC495
import LRSpectrumFull.L5S4.LinRQSC496
import LRSpectrumFull.L5S4.LinRQSC497
import LRSpectrumFull.L5S4.LinRQSC498
import LRSpectrumFull.L5S4.LinRQSC499
import LRSpectrumFull.L5S4.LinRQSC500
import LRSpectrumFull.L5S4.LinRQSC501
import LRSpectrumFull.L5S4.LinRQSC502
import LRSpectrumFull.L5S4.LinRQSC503
import LRSpectrumFull.L5S4.LinRQSC504
import LRSpectrumFull.L5S4.LinRQSC505
import LRSpectrumFull.L5S4.LinRQSC506
import LRSpectrumFull.L5S4.LinRQSC507
import LRSpectrumFull.L5S4.LinRQSC508
import LRSpectrumFull.L5S4.LinRQSC509
import LRSpectrumFull.L5S4.LinRQSC510
import LRSpectrumFull.L5S4.LinRQSC511

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG15

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC480.blobs ++ (LinRQSC481.blobs ++ (LinRQSC482.blobs ++ (LinRQSC483.blobs ++ (LinRQSC484.blobs ++ (LinRQSC485.blobs ++ (LinRQSC486.blobs ++ (LinRQSC487.blobs ++ (LinRQSC488.blobs ++ (LinRQSC489.blobs ++ (LinRQSC490.blobs ++ (LinRQSC491.blobs ++ (LinRQSC492.blobs ++ (LinRQSC493.blobs ++ (LinRQSC494.blobs ++ (LinRQSC495.blobs ++ (LinRQSC496.blobs ++ (LinRQSC497.blobs ++ (LinRQSC498.blobs ++ (LinRQSC499.blobs ++ (LinRQSC500.blobs ++ (LinRQSC501.blobs ++ (LinRQSC502.blobs ++ (LinRQSC503.blobs ++ (LinRQSC504.blobs ++ (LinRQSC505.blobs ++ (LinRQSC506.blobs ++ (LinRQSC507.blobs ++ (LinRQSC508.blobs ++ (LinRQSC509.blobs ++ (LinRQSC510.blobs ++ (LinRQSC511.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC480.ok (chunksR_ok_append LinRQSC481.ok (chunksR_ok_append LinRQSC482.ok (chunksR_ok_append LinRQSC483.ok (chunksR_ok_append LinRQSC484.ok (chunksR_ok_append LinRQSC485.ok (chunksR_ok_append LinRQSC486.ok (chunksR_ok_append LinRQSC487.ok (chunksR_ok_append LinRQSC488.ok (chunksR_ok_append LinRQSC489.ok (chunksR_ok_append LinRQSC490.ok (chunksR_ok_append LinRQSC491.ok (chunksR_ok_append LinRQSC492.ok (chunksR_ok_append LinRQSC493.ok (chunksR_ok_append LinRQSC494.ok (chunksR_ok_append LinRQSC495.ok (chunksR_ok_append LinRQSC496.ok (chunksR_ok_append LinRQSC497.ok (chunksR_ok_append LinRQSC498.ok (chunksR_ok_append LinRQSC499.ok (chunksR_ok_append LinRQSC500.ok (chunksR_ok_append LinRQSC501.ok (chunksR_ok_append LinRQSC502.ok (chunksR_ok_append LinRQSC503.ok (chunksR_ok_append LinRQSC504.ok (chunksR_ok_append LinRQSC505.ok (chunksR_ok_append LinRQSC506.ok (chunksR_ok_append LinRQSC507.ok (chunksR_ok_append LinRQSC508.ok (chunksR_ok_append LinRQSC509.ok (chunksR_ok_append LinRQSC510.ok (LinRQSC511.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG15
end L5S4
end LRSpectrumFull

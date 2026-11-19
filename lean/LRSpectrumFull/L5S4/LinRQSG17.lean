/-
# L5S4.LinRQSG17 : node S group 17 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC544
import LRSpectrumFull.L5S4.LinRQSC545
import LRSpectrumFull.L5S4.LinRQSC546
import LRSpectrumFull.L5S4.LinRQSC547
import LRSpectrumFull.L5S4.LinRQSC548
import LRSpectrumFull.L5S4.LinRQSC549
import LRSpectrumFull.L5S4.LinRQSC550
import LRSpectrumFull.L5S4.LinRQSC551
import LRSpectrumFull.L5S4.LinRQSC552
import LRSpectrumFull.L5S4.LinRQSC553
import LRSpectrumFull.L5S4.LinRQSC554
import LRSpectrumFull.L5S4.LinRQSC555
import LRSpectrumFull.L5S4.LinRQSC556
import LRSpectrumFull.L5S4.LinRQSC557
import LRSpectrumFull.L5S4.LinRQSC558
import LRSpectrumFull.L5S4.LinRQSC559
import LRSpectrumFull.L5S4.LinRQSC560
import LRSpectrumFull.L5S4.LinRQSC561
import LRSpectrumFull.L5S4.LinRQSC562
import LRSpectrumFull.L5S4.LinRQSC563
import LRSpectrumFull.L5S4.LinRQSC564
import LRSpectrumFull.L5S4.LinRQSC565
import LRSpectrumFull.L5S4.LinRQSC566
import LRSpectrumFull.L5S4.LinRQSC567
import LRSpectrumFull.L5S4.LinRQSC568
import LRSpectrumFull.L5S4.LinRQSC569
import LRSpectrumFull.L5S4.LinRQSC570
import LRSpectrumFull.L5S4.LinRQSC571
import LRSpectrumFull.L5S4.LinRQSC572
import LRSpectrumFull.L5S4.LinRQSC573
import LRSpectrumFull.L5S4.LinRQSC574
import LRSpectrumFull.L5S4.LinRQSC575

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG17

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC544.blobs ++ (LinRQSC545.blobs ++ (LinRQSC546.blobs ++ (LinRQSC547.blobs ++ (LinRQSC548.blobs ++ (LinRQSC549.blobs ++ (LinRQSC550.blobs ++ (LinRQSC551.blobs ++ (LinRQSC552.blobs ++ (LinRQSC553.blobs ++ (LinRQSC554.blobs ++ (LinRQSC555.blobs ++ (LinRQSC556.blobs ++ (LinRQSC557.blobs ++ (LinRQSC558.blobs ++ (LinRQSC559.blobs ++ (LinRQSC560.blobs ++ (LinRQSC561.blobs ++ (LinRQSC562.blobs ++ (LinRQSC563.blobs ++ (LinRQSC564.blobs ++ (LinRQSC565.blobs ++ (LinRQSC566.blobs ++ (LinRQSC567.blobs ++ (LinRQSC568.blobs ++ (LinRQSC569.blobs ++ (LinRQSC570.blobs ++ (LinRQSC571.blobs ++ (LinRQSC572.blobs ++ (LinRQSC573.blobs ++ (LinRQSC574.blobs ++ (LinRQSC575.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC544.ok (chunksR_ok_append LinRQSC545.ok (chunksR_ok_append LinRQSC546.ok (chunksR_ok_append LinRQSC547.ok (chunksR_ok_append LinRQSC548.ok (chunksR_ok_append LinRQSC549.ok (chunksR_ok_append LinRQSC550.ok (chunksR_ok_append LinRQSC551.ok (chunksR_ok_append LinRQSC552.ok (chunksR_ok_append LinRQSC553.ok (chunksR_ok_append LinRQSC554.ok (chunksR_ok_append LinRQSC555.ok (chunksR_ok_append LinRQSC556.ok (chunksR_ok_append LinRQSC557.ok (chunksR_ok_append LinRQSC558.ok (chunksR_ok_append LinRQSC559.ok (chunksR_ok_append LinRQSC560.ok (chunksR_ok_append LinRQSC561.ok (chunksR_ok_append LinRQSC562.ok (chunksR_ok_append LinRQSC563.ok (chunksR_ok_append LinRQSC564.ok (chunksR_ok_append LinRQSC565.ok (chunksR_ok_append LinRQSC566.ok (chunksR_ok_append LinRQSC567.ok (chunksR_ok_append LinRQSC568.ok (chunksR_ok_append LinRQSC569.ok (chunksR_ok_append LinRQSC570.ok (chunksR_ok_append LinRQSC571.ok (chunksR_ok_append LinRQSC572.ok (chunksR_ok_append LinRQSC573.ok (chunksR_ok_append LinRQSC574.ok (LinRQSC575.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG17
end L5S4
end LRSpectrumFull

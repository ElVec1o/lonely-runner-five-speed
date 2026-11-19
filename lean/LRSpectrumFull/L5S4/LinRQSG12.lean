/-
# L5S4.LinRQSG12 : node S group 12 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC384
import LRSpectrumFull.L5S4.LinRQSC385
import LRSpectrumFull.L5S4.LinRQSC386
import LRSpectrumFull.L5S4.LinRQSC387
import LRSpectrumFull.L5S4.LinRQSC388
import LRSpectrumFull.L5S4.LinRQSC389
import LRSpectrumFull.L5S4.LinRQSC390
import LRSpectrumFull.L5S4.LinRQSC391
import LRSpectrumFull.L5S4.LinRQSC392
import LRSpectrumFull.L5S4.LinRQSC393
import LRSpectrumFull.L5S4.LinRQSC394
import LRSpectrumFull.L5S4.LinRQSC395
import LRSpectrumFull.L5S4.LinRQSC396
import LRSpectrumFull.L5S4.LinRQSC397
import LRSpectrumFull.L5S4.LinRQSC398
import LRSpectrumFull.L5S4.LinRQSC399
import LRSpectrumFull.L5S4.LinRQSC400
import LRSpectrumFull.L5S4.LinRQSC401
import LRSpectrumFull.L5S4.LinRQSC402
import LRSpectrumFull.L5S4.LinRQSC403
import LRSpectrumFull.L5S4.LinRQSC404
import LRSpectrumFull.L5S4.LinRQSC405
import LRSpectrumFull.L5S4.LinRQSC406
import LRSpectrumFull.L5S4.LinRQSC407
import LRSpectrumFull.L5S4.LinRQSC408
import LRSpectrumFull.L5S4.LinRQSC409
import LRSpectrumFull.L5S4.LinRQSC410
import LRSpectrumFull.L5S4.LinRQSC411
import LRSpectrumFull.L5S4.LinRQSC412
import LRSpectrumFull.L5S4.LinRQSC413
import LRSpectrumFull.L5S4.LinRQSC414
import LRSpectrumFull.L5S4.LinRQSC415

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG12

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC384.blobs ++ (LinRQSC385.blobs ++ (LinRQSC386.blobs ++ (LinRQSC387.blobs ++ (LinRQSC388.blobs ++ (LinRQSC389.blobs ++ (LinRQSC390.blobs ++ (LinRQSC391.blobs ++ (LinRQSC392.blobs ++ (LinRQSC393.blobs ++ (LinRQSC394.blobs ++ (LinRQSC395.blobs ++ (LinRQSC396.blobs ++ (LinRQSC397.blobs ++ (LinRQSC398.blobs ++ (LinRQSC399.blobs ++ (LinRQSC400.blobs ++ (LinRQSC401.blobs ++ (LinRQSC402.blobs ++ (LinRQSC403.blobs ++ (LinRQSC404.blobs ++ (LinRQSC405.blobs ++ (LinRQSC406.blobs ++ (LinRQSC407.blobs ++ (LinRQSC408.blobs ++ (LinRQSC409.blobs ++ (LinRQSC410.blobs ++ (LinRQSC411.blobs ++ (LinRQSC412.blobs ++ (LinRQSC413.blobs ++ (LinRQSC414.blobs ++ (LinRQSC415.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC384.ok (chunksR_ok_append LinRQSC385.ok (chunksR_ok_append LinRQSC386.ok (chunksR_ok_append LinRQSC387.ok (chunksR_ok_append LinRQSC388.ok (chunksR_ok_append LinRQSC389.ok (chunksR_ok_append LinRQSC390.ok (chunksR_ok_append LinRQSC391.ok (chunksR_ok_append LinRQSC392.ok (chunksR_ok_append LinRQSC393.ok (chunksR_ok_append LinRQSC394.ok (chunksR_ok_append LinRQSC395.ok (chunksR_ok_append LinRQSC396.ok (chunksR_ok_append LinRQSC397.ok (chunksR_ok_append LinRQSC398.ok (chunksR_ok_append LinRQSC399.ok (chunksR_ok_append LinRQSC400.ok (chunksR_ok_append LinRQSC401.ok (chunksR_ok_append LinRQSC402.ok (chunksR_ok_append LinRQSC403.ok (chunksR_ok_append LinRQSC404.ok (chunksR_ok_append LinRQSC405.ok (chunksR_ok_append LinRQSC406.ok (chunksR_ok_append LinRQSC407.ok (chunksR_ok_append LinRQSC408.ok (chunksR_ok_append LinRQSC409.ok (chunksR_ok_append LinRQSC410.ok (chunksR_ok_append LinRQSC411.ok (chunksR_ok_append LinRQSC412.ok (chunksR_ok_append LinRQSC413.ok (chunksR_ok_append LinRQSC414.ok (LinRQSC415.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG12
end L5S4
end LRSpectrumFull

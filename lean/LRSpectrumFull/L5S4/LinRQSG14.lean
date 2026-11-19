/-
# L5S4.LinRQSG14 : node S group 14 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC448
import LRSpectrumFull.L5S4.LinRQSC449
import LRSpectrumFull.L5S4.LinRQSC450
import LRSpectrumFull.L5S4.LinRQSC451
import LRSpectrumFull.L5S4.LinRQSC452
import LRSpectrumFull.L5S4.LinRQSC453
import LRSpectrumFull.L5S4.LinRQSC454
import LRSpectrumFull.L5S4.LinRQSC455
import LRSpectrumFull.L5S4.LinRQSC456
import LRSpectrumFull.L5S4.LinRQSC457
import LRSpectrumFull.L5S4.LinRQSC458
import LRSpectrumFull.L5S4.LinRQSC459
import LRSpectrumFull.L5S4.LinRQSC460
import LRSpectrumFull.L5S4.LinRQSC461
import LRSpectrumFull.L5S4.LinRQSC462
import LRSpectrumFull.L5S4.LinRQSC463
import LRSpectrumFull.L5S4.LinRQSC464
import LRSpectrumFull.L5S4.LinRQSC465
import LRSpectrumFull.L5S4.LinRQSC466
import LRSpectrumFull.L5S4.LinRQSC467
import LRSpectrumFull.L5S4.LinRQSC468
import LRSpectrumFull.L5S4.LinRQSC469
import LRSpectrumFull.L5S4.LinRQSC470
import LRSpectrumFull.L5S4.LinRQSC471
import LRSpectrumFull.L5S4.LinRQSC472
import LRSpectrumFull.L5S4.LinRQSC473
import LRSpectrumFull.L5S4.LinRQSC474
import LRSpectrumFull.L5S4.LinRQSC475
import LRSpectrumFull.L5S4.LinRQSC476
import LRSpectrumFull.L5S4.LinRQSC477
import LRSpectrumFull.L5S4.LinRQSC478
import LRSpectrumFull.L5S4.LinRQSC479

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG14

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC448.blobs ++ (LinRQSC449.blobs ++ (LinRQSC450.blobs ++ (LinRQSC451.blobs ++ (LinRQSC452.blobs ++ (LinRQSC453.blobs ++ (LinRQSC454.blobs ++ (LinRQSC455.blobs ++ (LinRQSC456.blobs ++ (LinRQSC457.blobs ++ (LinRQSC458.blobs ++ (LinRQSC459.blobs ++ (LinRQSC460.blobs ++ (LinRQSC461.blobs ++ (LinRQSC462.blobs ++ (LinRQSC463.blobs ++ (LinRQSC464.blobs ++ (LinRQSC465.blobs ++ (LinRQSC466.blobs ++ (LinRQSC467.blobs ++ (LinRQSC468.blobs ++ (LinRQSC469.blobs ++ (LinRQSC470.blobs ++ (LinRQSC471.blobs ++ (LinRQSC472.blobs ++ (LinRQSC473.blobs ++ (LinRQSC474.blobs ++ (LinRQSC475.blobs ++ (LinRQSC476.blobs ++ (LinRQSC477.blobs ++ (LinRQSC478.blobs ++ (LinRQSC479.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC448.ok (chunksR_ok_append LinRQSC449.ok (chunksR_ok_append LinRQSC450.ok (chunksR_ok_append LinRQSC451.ok (chunksR_ok_append LinRQSC452.ok (chunksR_ok_append LinRQSC453.ok (chunksR_ok_append LinRQSC454.ok (chunksR_ok_append LinRQSC455.ok (chunksR_ok_append LinRQSC456.ok (chunksR_ok_append LinRQSC457.ok (chunksR_ok_append LinRQSC458.ok (chunksR_ok_append LinRQSC459.ok (chunksR_ok_append LinRQSC460.ok (chunksR_ok_append LinRQSC461.ok (chunksR_ok_append LinRQSC462.ok (chunksR_ok_append LinRQSC463.ok (chunksR_ok_append LinRQSC464.ok (chunksR_ok_append LinRQSC465.ok (chunksR_ok_append LinRQSC466.ok (chunksR_ok_append LinRQSC467.ok (chunksR_ok_append LinRQSC468.ok (chunksR_ok_append LinRQSC469.ok (chunksR_ok_append LinRQSC470.ok (chunksR_ok_append LinRQSC471.ok (chunksR_ok_append LinRQSC472.ok (chunksR_ok_append LinRQSC473.ok (chunksR_ok_append LinRQSC474.ok (chunksR_ok_append LinRQSC475.ok (chunksR_ok_append LinRQSC476.ok (chunksR_ok_append LinRQSC477.ok (chunksR_ok_append LinRQSC478.ok (LinRQSC479.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG14
end L5S4
end LRSpectrumFull

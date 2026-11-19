/-
# L5S4.LinRQSG16 : node S group 16 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC512
import LRSpectrumFull.L5S4.LinRQSC513
import LRSpectrumFull.L5S4.LinRQSC514
import LRSpectrumFull.L5S4.LinRQSC515
import LRSpectrumFull.L5S4.LinRQSC516
import LRSpectrumFull.L5S4.LinRQSC517
import LRSpectrumFull.L5S4.LinRQSC518
import LRSpectrumFull.L5S4.LinRQSC519
import LRSpectrumFull.L5S4.LinRQSC520
import LRSpectrumFull.L5S4.LinRQSC521
import LRSpectrumFull.L5S4.LinRQSC522
import LRSpectrumFull.L5S4.LinRQSC523
import LRSpectrumFull.L5S4.LinRQSC524
import LRSpectrumFull.L5S4.LinRQSC525
import LRSpectrumFull.L5S4.LinRQSC526
import LRSpectrumFull.L5S4.LinRQSC527
import LRSpectrumFull.L5S4.LinRQSC528
import LRSpectrumFull.L5S4.LinRQSC529
import LRSpectrumFull.L5S4.LinRQSC530
import LRSpectrumFull.L5S4.LinRQSC531
import LRSpectrumFull.L5S4.LinRQSC532
import LRSpectrumFull.L5S4.LinRQSC533
import LRSpectrumFull.L5S4.LinRQSC534
import LRSpectrumFull.L5S4.LinRQSC535
import LRSpectrumFull.L5S4.LinRQSC536
import LRSpectrumFull.L5S4.LinRQSC537
import LRSpectrumFull.L5S4.LinRQSC538
import LRSpectrumFull.L5S4.LinRQSC539
import LRSpectrumFull.L5S4.LinRQSC540
import LRSpectrumFull.L5S4.LinRQSC541
import LRSpectrumFull.L5S4.LinRQSC542
import LRSpectrumFull.L5S4.LinRQSC543

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG16

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC512.blobs ++ (LinRQSC513.blobs ++ (LinRQSC514.blobs ++ (LinRQSC515.blobs ++ (LinRQSC516.blobs ++ (LinRQSC517.blobs ++ (LinRQSC518.blobs ++ (LinRQSC519.blobs ++ (LinRQSC520.blobs ++ (LinRQSC521.blobs ++ (LinRQSC522.blobs ++ (LinRQSC523.blobs ++ (LinRQSC524.blobs ++ (LinRQSC525.blobs ++ (LinRQSC526.blobs ++ (LinRQSC527.blobs ++ (LinRQSC528.blobs ++ (LinRQSC529.blobs ++ (LinRQSC530.blobs ++ (LinRQSC531.blobs ++ (LinRQSC532.blobs ++ (LinRQSC533.blobs ++ (LinRQSC534.blobs ++ (LinRQSC535.blobs ++ (LinRQSC536.blobs ++ (LinRQSC537.blobs ++ (LinRQSC538.blobs ++ (LinRQSC539.blobs ++ (LinRQSC540.blobs ++ (LinRQSC541.blobs ++ (LinRQSC542.blobs ++ (LinRQSC543.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC512.ok (chunksR_ok_append LinRQSC513.ok (chunksR_ok_append LinRQSC514.ok (chunksR_ok_append LinRQSC515.ok (chunksR_ok_append LinRQSC516.ok (chunksR_ok_append LinRQSC517.ok (chunksR_ok_append LinRQSC518.ok (chunksR_ok_append LinRQSC519.ok (chunksR_ok_append LinRQSC520.ok (chunksR_ok_append LinRQSC521.ok (chunksR_ok_append LinRQSC522.ok (chunksR_ok_append LinRQSC523.ok (chunksR_ok_append LinRQSC524.ok (chunksR_ok_append LinRQSC525.ok (chunksR_ok_append LinRQSC526.ok (chunksR_ok_append LinRQSC527.ok (chunksR_ok_append LinRQSC528.ok (chunksR_ok_append LinRQSC529.ok (chunksR_ok_append LinRQSC530.ok (chunksR_ok_append LinRQSC531.ok (chunksR_ok_append LinRQSC532.ok (chunksR_ok_append LinRQSC533.ok (chunksR_ok_append LinRQSC534.ok (chunksR_ok_append LinRQSC535.ok (chunksR_ok_append LinRQSC536.ok (chunksR_ok_append LinRQSC537.ok (chunksR_ok_append LinRQSC538.ok (chunksR_ok_append LinRQSC539.ok (chunksR_ok_append LinRQSC540.ok (chunksR_ok_append LinRQSC541.ok (chunksR_ok_append LinRQSC542.ok (LinRQSC543.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG16
end L5S4
end LRSpectrumFull

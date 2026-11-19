/-
# L5S4.LinRQSG13 : node S group 13 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC416
import LRSpectrumFull.L5S4.LinRQSC417
import LRSpectrumFull.L5S4.LinRQSC418
import LRSpectrumFull.L5S4.LinRQSC419
import LRSpectrumFull.L5S4.LinRQSC420
import LRSpectrumFull.L5S4.LinRQSC421
import LRSpectrumFull.L5S4.LinRQSC422
import LRSpectrumFull.L5S4.LinRQSC423
import LRSpectrumFull.L5S4.LinRQSC424
import LRSpectrumFull.L5S4.LinRQSC425
import LRSpectrumFull.L5S4.LinRQSC426
import LRSpectrumFull.L5S4.LinRQSC427
import LRSpectrumFull.L5S4.LinRQSC428
import LRSpectrumFull.L5S4.LinRQSC429
import LRSpectrumFull.L5S4.LinRQSC430
import LRSpectrumFull.L5S4.LinRQSC431
import LRSpectrumFull.L5S4.LinRQSC432
import LRSpectrumFull.L5S4.LinRQSC433
import LRSpectrumFull.L5S4.LinRQSC434
import LRSpectrumFull.L5S4.LinRQSC435
import LRSpectrumFull.L5S4.LinRQSC436
import LRSpectrumFull.L5S4.LinRQSC437
import LRSpectrumFull.L5S4.LinRQSC438
import LRSpectrumFull.L5S4.LinRQSC439
import LRSpectrumFull.L5S4.LinRQSC440
import LRSpectrumFull.L5S4.LinRQSC441
import LRSpectrumFull.L5S4.LinRQSC442
import LRSpectrumFull.L5S4.LinRQSC443
import LRSpectrumFull.L5S4.LinRQSC444
import LRSpectrumFull.L5S4.LinRQSC445
import LRSpectrumFull.L5S4.LinRQSC446
import LRSpectrumFull.L5S4.LinRQSC447

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG13

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC416.blobs ++ (LinRQSC417.blobs ++ (LinRQSC418.blobs ++ (LinRQSC419.blobs ++ (LinRQSC420.blobs ++ (LinRQSC421.blobs ++ (LinRQSC422.blobs ++ (LinRQSC423.blobs ++ (LinRQSC424.blobs ++ (LinRQSC425.blobs ++ (LinRQSC426.blobs ++ (LinRQSC427.blobs ++ (LinRQSC428.blobs ++ (LinRQSC429.blobs ++ (LinRQSC430.blobs ++ (LinRQSC431.blobs ++ (LinRQSC432.blobs ++ (LinRQSC433.blobs ++ (LinRQSC434.blobs ++ (LinRQSC435.blobs ++ (LinRQSC436.blobs ++ (LinRQSC437.blobs ++ (LinRQSC438.blobs ++ (LinRQSC439.blobs ++ (LinRQSC440.blobs ++ (LinRQSC441.blobs ++ (LinRQSC442.blobs ++ (LinRQSC443.blobs ++ (LinRQSC444.blobs ++ (LinRQSC445.blobs ++ (LinRQSC446.blobs ++ (LinRQSC447.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC416.ok (chunksR_ok_append LinRQSC417.ok (chunksR_ok_append LinRQSC418.ok (chunksR_ok_append LinRQSC419.ok (chunksR_ok_append LinRQSC420.ok (chunksR_ok_append LinRQSC421.ok (chunksR_ok_append LinRQSC422.ok (chunksR_ok_append LinRQSC423.ok (chunksR_ok_append LinRQSC424.ok (chunksR_ok_append LinRQSC425.ok (chunksR_ok_append LinRQSC426.ok (chunksR_ok_append LinRQSC427.ok (chunksR_ok_append LinRQSC428.ok (chunksR_ok_append LinRQSC429.ok (chunksR_ok_append LinRQSC430.ok (chunksR_ok_append LinRQSC431.ok (chunksR_ok_append LinRQSC432.ok (chunksR_ok_append LinRQSC433.ok (chunksR_ok_append LinRQSC434.ok (chunksR_ok_append LinRQSC435.ok (chunksR_ok_append LinRQSC436.ok (chunksR_ok_append LinRQSC437.ok (chunksR_ok_append LinRQSC438.ok (chunksR_ok_append LinRQSC439.ok (chunksR_ok_append LinRQSC440.ok (chunksR_ok_append LinRQSC441.ok (chunksR_ok_append LinRQSC442.ok (chunksR_ok_append LinRQSC443.ok (chunksR_ok_append LinRQSC444.ok (chunksR_ok_append LinRQSC445.ok (chunksR_ok_append LinRQSC446.ok (LinRQSC447.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG13
end L5S4
end LRSpectrumFull

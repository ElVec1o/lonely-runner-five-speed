/-
# L5S4.LinRQSG18 : node S group 18 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC576
import LRSpectrumFull.L5S4.LinRQSC577
import LRSpectrumFull.L5S4.LinRQSC578
import LRSpectrumFull.L5S4.LinRQSC579
import LRSpectrumFull.L5S4.LinRQSC580
import LRSpectrumFull.L5S4.LinRQSC581
import LRSpectrumFull.L5S4.LinRQSC582
import LRSpectrumFull.L5S4.LinRQSC583
import LRSpectrumFull.L5S4.LinRQSC584
import LRSpectrumFull.L5S4.LinRQSC585
import LRSpectrumFull.L5S4.LinRQSC586
import LRSpectrumFull.L5S4.LinRQSC587
import LRSpectrumFull.L5S4.LinRQSC588
import LRSpectrumFull.L5S4.LinRQSC589
import LRSpectrumFull.L5S4.LinRQSC590
import LRSpectrumFull.L5S4.LinRQSC591
import LRSpectrumFull.L5S4.LinRQSC592
import LRSpectrumFull.L5S4.LinRQSC593
import LRSpectrumFull.L5S4.LinRQSC594
import LRSpectrumFull.L5S4.LinRQSC595
import LRSpectrumFull.L5S4.LinRQSC596
import LRSpectrumFull.L5S4.LinRQSC597
import LRSpectrumFull.L5S4.LinRQSC598
import LRSpectrumFull.L5S4.LinRQSC599
import LRSpectrumFull.L5S4.LinRQSC600
import LRSpectrumFull.L5S4.LinRQSC601
import LRSpectrumFull.L5S4.LinRQSC602
import LRSpectrumFull.L5S4.LinRQSC603
import LRSpectrumFull.L5S4.LinRQSC604
import LRSpectrumFull.L5S4.LinRQSC605
import LRSpectrumFull.L5S4.LinRQSC606
import LRSpectrumFull.L5S4.LinRQSC607

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG18

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC576.blobs ++ (LinRQSC577.blobs ++ (LinRQSC578.blobs ++ (LinRQSC579.blobs ++ (LinRQSC580.blobs ++ (LinRQSC581.blobs ++ (LinRQSC582.blobs ++ (LinRQSC583.blobs ++ (LinRQSC584.blobs ++ (LinRQSC585.blobs ++ (LinRQSC586.blobs ++ (LinRQSC587.blobs ++ (LinRQSC588.blobs ++ (LinRQSC589.blobs ++ (LinRQSC590.blobs ++ (LinRQSC591.blobs ++ (LinRQSC592.blobs ++ (LinRQSC593.blobs ++ (LinRQSC594.blobs ++ (LinRQSC595.blobs ++ (LinRQSC596.blobs ++ (LinRQSC597.blobs ++ (LinRQSC598.blobs ++ (LinRQSC599.blobs ++ (LinRQSC600.blobs ++ (LinRQSC601.blobs ++ (LinRQSC602.blobs ++ (LinRQSC603.blobs ++ (LinRQSC604.blobs ++ (LinRQSC605.blobs ++ (LinRQSC606.blobs ++ (LinRQSC607.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC576.ok (chunksR_ok_append LinRQSC577.ok (chunksR_ok_append LinRQSC578.ok (chunksR_ok_append LinRQSC579.ok (chunksR_ok_append LinRQSC580.ok (chunksR_ok_append LinRQSC581.ok (chunksR_ok_append LinRQSC582.ok (chunksR_ok_append LinRQSC583.ok (chunksR_ok_append LinRQSC584.ok (chunksR_ok_append LinRQSC585.ok (chunksR_ok_append LinRQSC586.ok (chunksR_ok_append LinRQSC587.ok (chunksR_ok_append LinRQSC588.ok (chunksR_ok_append LinRQSC589.ok (chunksR_ok_append LinRQSC590.ok (chunksR_ok_append LinRQSC591.ok (chunksR_ok_append LinRQSC592.ok (chunksR_ok_append LinRQSC593.ok (chunksR_ok_append LinRQSC594.ok (chunksR_ok_append LinRQSC595.ok (chunksR_ok_append LinRQSC596.ok (chunksR_ok_append LinRQSC597.ok (chunksR_ok_append LinRQSC598.ok (chunksR_ok_append LinRQSC599.ok (chunksR_ok_append LinRQSC600.ok (chunksR_ok_append LinRQSC601.ok (chunksR_ok_append LinRQSC602.ok (chunksR_ok_append LinRQSC603.ok (chunksR_ok_append LinRQSC604.ok (chunksR_ok_append LinRQSC605.ok (chunksR_ok_append LinRQSC606.ok (LinRQSC607.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG18
end L5S4
end LRSpectrumFull

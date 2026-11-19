/-
# L5S4.LinRQSG19 : node S group 19 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC608
import LRSpectrumFull.L5S4.LinRQSC609
import LRSpectrumFull.L5S4.LinRQSC610
import LRSpectrumFull.L5S4.LinRQSC611
import LRSpectrumFull.L5S4.LinRQSC612
import LRSpectrumFull.L5S4.LinRQSC613
import LRSpectrumFull.L5S4.LinRQSC614
import LRSpectrumFull.L5S4.LinRQSC615
import LRSpectrumFull.L5S4.LinRQSC616
import LRSpectrumFull.L5S4.LinRQSC617
import LRSpectrumFull.L5S4.LinRQSC618
import LRSpectrumFull.L5S4.LinRQSC619
import LRSpectrumFull.L5S4.LinRQSC620
import LRSpectrumFull.L5S4.LinRQSC621
import LRSpectrumFull.L5S4.LinRQSC622
import LRSpectrumFull.L5S4.LinRQSC623
import LRSpectrumFull.L5S4.LinRQSC624
import LRSpectrumFull.L5S4.LinRQSC625
import LRSpectrumFull.L5S4.LinRQSC626
import LRSpectrumFull.L5S4.LinRQSC627
import LRSpectrumFull.L5S4.LinRQSC628
import LRSpectrumFull.L5S4.LinRQSC629
import LRSpectrumFull.L5S4.LinRQSC630
import LRSpectrumFull.L5S4.LinRQSC631
import LRSpectrumFull.L5S4.LinRQSC632
import LRSpectrumFull.L5S4.LinRQSC633
import LRSpectrumFull.L5S4.LinRQSC634
import LRSpectrumFull.L5S4.LinRQSC635
import LRSpectrumFull.L5S4.LinRQSC636
import LRSpectrumFull.L5S4.LinRQSC637
import LRSpectrumFull.L5S4.LinRQSC638
import LRSpectrumFull.L5S4.LinRQSC639

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG19

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC608.blobs ++ (LinRQSC609.blobs ++ (LinRQSC610.blobs ++ (LinRQSC611.blobs ++ (LinRQSC612.blobs ++ (LinRQSC613.blobs ++ (LinRQSC614.blobs ++ (LinRQSC615.blobs ++ (LinRQSC616.blobs ++ (LinRQSC617.blobs ++ (LinRQSC618.blobs ++ (LinRQSC619.blobs ++ (LinRQSC620.blobs ++ (LinRQSC621.blobs ++ (LinRQSC622.blobs ++ (LinRQSC623.blobs ++ (LinRQSC624.blobs ++ (LinRQSC625.blobs ++ (LinRQSC626.blobs ++ (LinRQSC627.blobs ++ (LinRQSC628.blobs ++ (LinRQSC629.blobs ++ (LinRQSC630.blobs ++ (LinRQSC631.blobs ++ (LinRQSC632.blobs ++ (LinRQSC633.blobs ++ (LinRQSC634.blobs ++ (LinRQSC635.blobs ++ (LinRQSC636.blobs ++ (LinRQSC637.blobs ++ (LinRQSC638.blobs ++ (LinRQSC639.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC608.ok (chunksR_ok_append LinRQSC609.ok (chunksR_ok_append LinRQSC610.ok (chunksR_ok_append LinRQSC611.ok (chunksR_ok_append LinRQSC612.ok (chunksR_ok_append LinRQSC613.ok (chunksR_ok_append LinRQSC614.ok (chunksR_ok_append LinRQSC615.ok (chunksR_ok_append LinRQSC616.ok (chunksR_ok_append LinRQSC617.ok (chunksR_ok_append LinRQSC618.ok (chunksR_ok_append LinRQSC619.ok (chunksR_ok_append LinRQSC620.ok (chunksR_ok_append LinRQSC621.ok (chunksR_ok_append LinRQSC622.ok (chunksR_ok_append LinRQSC623.ok (chunksR_ok_append LinRQSC624.ok (chunksR_ok_append LinRQSC625.ok (chunksR_ok_append LinRQSC626.ok (chunksR_ok_append LinRQSC627.ok (chunksR_ok_append LinRQSC628.ok (chunksR_ok_append LinRQSC629.ok (chunksR_ok_append LinRQSC630.ok (chunksR_ok_append LinRQSC631.ok (chunksR_ok_append LinRQSC632.ok (chunksR_ok_append LinRQSC633.ok (chunksR_ok_append LinRQSC634.ok (chunksR_ok_append LinRQSC635.ok (chunksR_ok_append LinRQSC636.ok (chunksR_ok_append LinRQSC637.ok (chunksR_ok_append LinRQSC638.ok (LinRQSC639.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG19
end L5S4
end LRSpectrumFull

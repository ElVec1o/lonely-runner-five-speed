/-
# L5S4.LinRQSG20 : node S group 20 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC640
import LRSpectrumFull.L5S4.LinRQSC641
import LRSpectrumFull.L5S4.LinRQSC642
import LRSpectrumFull.L5S4.LinRQSC643
import LRSpectrumFull.L5S4.LinRQSC644
import LRSpectrumFull.L5S4.LinRQSC645
import LRSpectrumFull.L5S4.LinRQSC646
import LRSpectrumFull.L5S4.LinRQSC647
import LRSpectrumFull.L5S4.LinRQSC648
import LRSpectrumFull.L5S4.LinRQSC649
import LRSpectrumFull.L5S4.LinRQSC650
import LRSpectrumFull.L5S4.LinRQSC651
import LRSpectrumFull.L5S4.LinRQSC652
import LRSpectrumFull.L5S4.LinRQSC653
import LRSpectrumFull.L5S4.LinRQSC654
import LRSpectrumFull.L5S4.LinRQSC655
import LRSpectrumFull.L5S4.LinRQSC656
import LRSpectrumFull.L5S4.LinRQSC657
import LRSpectrumFull.L5S4.LinRQSC658
import LRSpectrumFull.L5S4.LinRQSC659
import LRSpectrumFull.L5S4.LinRQSC660
import LRSpectrumFull.L5S4.LinRQSC661
import LRSpectrumFull.L5S4.LinRQSC662
import LRSpectrumFull.L5S4.LinRQSC663
import LRSpectrumFull.L5S4.LinRQSC664
import LRSpectrumFull.L5S4.LinRQSC665
import LRSpectrumFull.L5S4.LinRQSC666
import LRSpectrumFull.L5S4.LinRQSC667
import LRSpectrumFull.L5S4.LinRQSC668
import LRSpectrumFull.L5S4.LinRQSC669
import LRSpectrumFull.L5S4.LinRQSC670
import LRSpectrumFull.L5S4.LinRQSC671

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG20

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC640.blobs ++ (LinRQSC641.blobs ++ (LinRQSC642.blobs ++ (LinRQSC643.blobs ++ (LinRQSC644.blobs ++ (LinRQSC645.blobs ++ (LinRQSC646.blobs ++ (LinRQSC647.blobs ++ (LinRQSC648.blobs ++ (LinRQSC649.blobs ++ (LinRQSC650.blobs ++ (LinRQSC651.blobs ++ (LinRQSC652.blobs ++ (LinRQSC653.blobs ++ (LinRQSC654.blobs ++ (LinRQSC655.blobs ++ (LinRQSC656.blobs ++ (LinRQSC657.blobs ++ (LinRQSC658.blobs ++ (LinRQSC659.blobs ++ (LinRQSC660.blobs ++ (LinRQSC661.blobs ++ (LinRQSC662.blobs ++ (LinRQSC663.blobs ++ (LinRQSC664.blobs ++ (LinRQSC665.blobs ++ (LinRQSC666.blobs ++ (LinRQSC667.blobs ++ (LinRQSC668.blobs ++ (LinRQSC669.blobs ++ (LinRQSC670.blobs ++ (LinRQSC671.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC640.ok (chunksR_ok_append LinRQSC641.ok (chunksR_ok_append LinRQSC642.ok (chunksR_ok_append LinRQSC643.ok (chunksR_ok_append LinRQSC644.ok (chunksR_ok_append LinRQSC645.ok (chunksR_ok_append LinRQSC646.ok (chunksR_ok_append LinRQSC647.ok (chunksR_ok_append LinRQSC648.ok (chunksR_ok_append LinRQSC649.ok (chunksR_ok_append LinRQSC650.ok (chunksR_ok_append LinRQSC651.ok (chunksR_ok_append LinRQSC652.ok (chunksR_ok_append LinRQSC653.ok (chunksR_ok_append LinRQSC654.ok (chunksR_ok_append LinRQSC655.ok (chunksR_ok_append LinRQSC656.ok (chunksR_ok_append LinRQSC657.ok (chunksR_ok_append LinRQSC658.ok (chunksR_ok_append LinRQSC659.ok (chunksR_ok_append LinRQSC660.ok (chunksR_ok_append LinRQSC661.ok (chunksR_ok_append LinRQSC662.ok (chunksR_ok_append LinRQSC663.ok (chunksR_ok_append LinRQSC664.ok (chunksR_ok_append LinRQSC665.ok (chunksR_ok_append LinRQSC666.ok (chunksR_ok_append LinRQSC667.ok (chunksR_ok_append LinRQSC668.ok (chunksR_ok_append LinRQSC669.ok (chunksR_ok_append LinRQSC670.ok (LinRQSC671.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG20
end L5S4
end LRSpectrumFull

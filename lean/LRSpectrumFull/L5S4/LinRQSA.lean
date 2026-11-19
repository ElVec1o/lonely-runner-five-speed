/-
# L5S4.LinRQSA : node S assembly of 33 groups
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSG0
import LRSpectrumFull.L5S4.LinRQSG1
import LRSpectrumFull.L5S4.LinRQSG2
import LRSpectrumFull.L5S4.LinRQSG3
import LRSpectrumFull.L5S4.LinRQSG4
import LRSpectrumFull.L5S4.LinRQSG5
import LRSpectrumFull.L5S4.LinRQSG6
import LRSpectrumFull.L5S4.LinRQSG7
import LRSpectrumFull.L5S4.LinRQSG8
import LRSpectrumFull.L5S4.LinRQSG9
import LRSpectrumFull.L5S4.LinRQSG10
import LRSpectrumFull.L5S4.LinRQSG11
import LRSpectrumFull.L5S4.LinRQSG12
import LRSpectrumFull.L5S4.LinRQSG13
import LRSpectrumFull.L5S4.LinRQSG14
import LRSpectrumFull.L5S4.LinRQSG15
import LRSpectrumFull.L5S4.LinRQSG16
import LRSpectrumFull.L5S4.LinRQSG17
import LRSpectrumFull.L5S4.LinRQSG18
import LRSpectrumFull.L5S4.LinRQSG19
import LRSpectrumFull.L5S4.LinRQSG20
import LRSpectrumFull.L5S4.LinRQSG21
import LRSpectrumFull.L5S4.LinRQSG22
import LRSpectrumFull.L5S4.LinRQSG23
import LRSpectrumFull.L5S4.LinRQSG24
import LRSpectrumFull.L5S4.LinRQSG25
import LRSpectrumFull.L5S4.LinRQSG26
import LRSpectrumFull.L5S4.LinRQSG27
import LRSpectrumFull.L5S4.LinRQSG28
import LRSpectrumFull.L5S4.LinRQSG29
import LRSpectrumFull.L5S4.LinRQSG30
import LRSpectrumFull.L5S4.LinRQSG31
import LRSpectrumFull.L5S4.LinRQSG32

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSA

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSG0.blobs ++ (LinRQSG1.blobs ++ (LinRQSG2.blobs ++ (LinRQSG3.blobs ++ (LinRQSG4.blobs ++ (LinRQSG5.blobs ++ (LinRQSG6.blobs ++ (LinRQSG7.blobs ++ (LinRQSG8.blobs ++ (LinRQSG9.blobs ++ (LinRQSG10.blobs ++ (LinRQSG11.blobs ++ (LinRQSG12.blobs ++ (LinRQSG13.blobs ++ (LinRQSG14.blobs ++ (LinRQSG15.blobs ++ (LinRQSG16.blobs ++ (LinRQSG17.blobs ++ (LinRQSG18.blobs ++ (LinRQSG19.blobs ++ (LinRQSG20.blobs ++ (LinRQSG21.blobs ++ (LinRQSG22.blobs ++ (LinRQSG23.blobs ++ (LinRQSG24.blobs ++ (LinRQSG25.blobs ++ (LinRQSG26.blobs ++ (LinRQSG27.blobs ++ (LinRQSG28.blobs ++ (LinRQSG29.blobs ++ (LinRQSG30.blobs ++ (LinRQSG31.blobs ++ (LinRQSG32.blobs))))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSG0.ok (chunksR_ok_append LinRQSG1.ok (chunksR_ok_append LinRQSG2.ok (chunksR_ok_append LinRQSG3.ok (chunksR_ok_append LinRQSG4.ok (chunksR_ok_append LinRQSG5.ok (chunksR_ok_append LinRQSG6.ok (chunksR_ok_append LinRQSG7.ok (chunksR_ok_append LinRQSG8.ok (chunksR_ok_append LinRQSG9.ok (chunksR_ok_append LinRQSG10.ok (chunksR_ok_append LinRQSG11.ok (chunksR_ok_append LinRQSG12.ok (chunksR_ok_append LinRQSG13.ok (chunksR_ok_append LinRQSG14.ok (chunksR_ok_append LinRQSG15.ok (chunksR_ok_append LinRQSG16.ok (chunksR_ok_append LinRQSG17.ok (chunksR_ok_append LinRQSG18.ok (chunksR_ok_append LinRQSG19.ok (chunksR_ok_append LinRQSG20.ok (chunksR_ok_append LinRQSG21.ok (chunksR_ok_append LinRQSG22.ok (chunksR_ok_append LinRQSG23.ok (chunksR_ok_append LinRQSG24.ok (chunksR_ok_append LinRQSG25.ok (chunksR_ok_append LinRQSG26.ok (chunksR_ok_append LinRQSG27.ok (chunksR_ok_append LinRQSG28.ok (chunksR_ok_append LinRQSG29.ok (chunksR_ok_append LinRQSG30.ok (chunksR_ok_append LinRQSG31.ok (LinRQSG32.ok))))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSA
end L5S4
end LRSpectrumFull

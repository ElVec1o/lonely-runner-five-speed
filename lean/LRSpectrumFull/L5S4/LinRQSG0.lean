/-
# L5S4.LinRQSG0 : node S group 0 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC0
import LRSpectrumFull.L5S4.LinRQSC1
import LRSpectrumFull.L5S4.LinRQSC2
import LRSpectrumFull.L5S4.LinRQSC3
import LRSpectrumFull.L5S4.LinRQSC4
import LRSpectrumFull.L5S4.LinRQSC5
import LRSpectrumFull.L5S4.LinRQSC6
import LRSpectrumFull.L5S4.LinRQSC7
import LRSpectrumFull.L5S4.LinRQSC8
import LRSpectrumFull.L5S4.LinRQSC9
import LRSpectrumFull.L5S4.LinRQSC10
import LRSpectrumFull.L5S4.LinRQSC11
import LRSpectrumFull.L5S4.LinRQSC12
import LRSpectrumFull.L5S4.LinRQSC13
import LRSpectrumFull.L5S4.LinRQSC14
import LRSpectrumFull.L5S4.LinRQSC15
import LRSpectrumFull.L5S4.LinRQSC16
import LRSpectrumFull.L5S4.LinRQSC17
import LRSpectrumFull.L5S4.LinRQSC18
import LRSpectrumFull.L5S4.LinRQSC19
import LRSpectrumFull.L5S4.LinRQSC20
import LRSpectrumFull.L5S4.LinRQSC21
import LRSpectrumFull.L5S4.LinRQSC22
import LRSpectrumFull.L5S4.LinRQSC23
import LRSpectrumFull.L5S4.LinRQSC24
import LRSpectrumFull.L5S4.LinRQSC25
import LRSpectrumFull.L5S4.LinRQSC26
import LRSpectrumFull.L5S4.LinRQSC27
import LRSpectrumFull.L5S4.LinRQSC28
import LRSpectrumFull.L5S4.LinRQSC29
import LRSpectrumFull.L5S4.LinRQSC30
import LRSpectrumFull.L5S4.LinRQSC31

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG0

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC0.blobs ++ (LinRQSC1.blobs ++ (LinRQSC2.blobs ++ (LinRQSC3.blobs ++ (LinRQSC4.blobs ++ (LinRQSC5.blobs ++ (LinRQSC6.blobs ++ (LinRQSC7.blobs ++ (LinRQSC8.blobs ++ (LinRQSC9.blobs ++ (LinRQSC10.blobs ++ (LinRQSC11.blobs ++ (LinRQSC12.blobs ++ (LinRQSC13.blobs ++ (LinRQSC14.blobs ++ (LinRQSC15.blobs ++ (LinRQSC16.blobs ++ (LinRQSC17.blobs ++ (LinRQSC18.blobs ++ (LinRQSC19.blobs ++ (LinRQSC20.blobs ++ (LinRQSC21.blobs ++ (LinRQSC22.blobs ++ (LinRQSC23.blobs ++ (LinRQSC24.blobs ++ (LinRQSC25.blobs ++ (LinRQSC26.blobs ++ (LinRQSC27.blobs ++ (LinRQSC28.blobs ++ (LinRQSC29.blobs ++ (LinRQSC30.blobs ++ (LinRQSC31.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC0.ok (chunksR_ok_append LinRQSC1.ok (chunksR_ok_append LinRQSC2.ok (chunksR_ok_append LinRQSC3.ok (chunksR_ok_append LinRQSC4.ok (chunksR_ok_append LinRQSC5.ok (chunksR_ok_append LinRQSC6.ok (chunksR_ok_append LinRQSC7.ok (chunksR_ok_append LinRQSC8.ok (chunksR_ok_append LinRQSC9.ok (chunksR_ok_append LinRQSC10.ok (chunksR_ok_append LinRQSC11.ok (chunksR_ok_append LinRQSC12.ok (chunksR_ok_append LinRQSC13.ok (chunksR_ok_append LinRQSC14.ok (chunksR_ok_append LinRQSC15.ok (chunksR_ok_append LinRQSC16.ok (chunksR_ok_append LinRQSC17.ok (chunksR_ok_append LinRQSC18.ok (chunksR_ok_append LinRQSC19.ok (chunksR_ok_append LinRQSC20.ok (chunksR_ok_append LinRQSC21.ok (chunksR_ok_append LinRQSC22.ok (chunksR_ok_append LinRQSC23.ok (chunksR_ok_append LinRQSC24.ok (chunksR_ok_append LinRQSC25.ok (chunksR_ok_append LinRQSC26.ok (chunksR_ok_append LinRQSC27.ok (chunksR_ok_append LinRQSC28.ok (chunksR_ok_append LinRQSC29.ok (chunksR_ok_append LinRQSC30.ok (LinRQSC31.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG0
end L5S4
end LRSpectrumFull

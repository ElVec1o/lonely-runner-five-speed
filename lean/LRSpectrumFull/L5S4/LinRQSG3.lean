/-
# L5S4.LinRQSG3 : node S group 3 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC96
import LRSpectrumFull.L5S4.LinRQSC97
import LRSpectrumFull.L5S4.LinRQSC98
import LRSpectrumFull.L5S4.LinRQSC99
import LRSpectrumFull.L5S4.LinRQSC100
import LRSpectrumFull.L5S4.LinRQSC101
import LRSpectrumFull.L5S4.LinRQSC102
import LRSpectrumFull.L5S4.LinRQSC103
import LRSpectrumFull.L5S4.LinRQSC104
import LRSpectrumFull.L5S4.LinRQSC105
import LRSpectrumFull.L5S4.LinRQSC106
import LRSpectrumFull.L5S4.LinRQSC107
import LRSpectrumFull.L5S4.LinRQSC108
import LRSpectrumFull.L5S4.LinRQSC109
import LRSpectrumFull.L5S4.LinRQSC110
import LRSpectrumFull.L5S4.LinRQSC111
import LRSpectrumFull.L5S4.LinRQSC112
import LRSpectrumFull.L5S4.LinRQSC113
import LRSpectrumFull.L5S4.LinRQSC114
import LRSpectrumFull.L5S4.LinRQSC115
import LRSpectrumFull.L5S4.LinRQSC116
import LRSpectrumFull.L5S4.LinRQSC117
import LRSpectrumFull.L5S4.LinRQSC118
import LRSpectrumFull.L5S4.LinRQSC119
import LRSpectrumFull.L5S4.LinRQSC120
import LRSpectrumFull.L5S4.LinRQSC121
import LRSpectrumFull.L5S4.LinRQSC122
import LRSpectrumFull.L5S4.LinRQSC123
import LRSpectrumFull.L5S4.LinRQSC124
import LRSpectrumFull.L5S4.LinRQSC125
import LRSpectrumFull.L5S4.LinRQSC126
import LRSpectrumFull.L5S4.LinRQSC127

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG3

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC96.blobs ++ (LinRQSC97.blobs ++ (LinRQSC98.blobs ++ (LinRQSC99.blobs ++ (LinRQSC100.blobs ++ (LinRQSC101.blobs ++ (LinRQSC102.blobs ++ (LinRQSC103.blobs ++ (LinRQSC104.blobs ++ (LinRQSC105.blobs ++ (LinRQSC106.blobs ++ (LinRQSC107.blobs ++ (LinRQSC108.blobs ++ (LinRQSC109.blobs ++ (LinRQSC110.blobs ++ (LinRQSC111.blobs ++ (LinRQSC112.blobs ++ (LinRQSC113.blobs ++ (LinRQSC114.blobs ++ (LinRQSC115.blobs ++ (LinRQSC116.blobs ++ (LinRQSC117.blobs ++ (LinRQSC118.blobs ++ (LinRQSC119.blobs ++ (LinRQSC120.blobs ++ (LinRQSC121.blobs ++ (LinRQSC122.blobs ++ (LinRQSC123.blobs ++ (LinRQSC124.blobs ++ (LinRQSC125.blobs ++ (LinRQSC126.blobs ++ (LinRQSC127.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC96.ok (chunksR_ok_append LinRQSC97.ok (chunksR_ok_append LinRQSC98.ok (chunksR_ok_append LinRQSC99.ok (chunksR_ok_append LinRQSC100.ok (chunksR_ok_append LinRQSC101.ok (chunksR_ok_append LinRQSC102.ok (chunksR_ok_append LinRQSC103.ok (chunksR_ok_append LinRQSC104.ok (chunksR_ok_append LinRQSC105.ok (chunksR_ok_append LinRQSC106.ok (chunksR_ok_append LinRQSC107.ok (chunksR_ok_append LinRQSC108.ok (chunksR_ok_append LinRQSC109.ok (chunksR_ok_append LinRQSC110.ok (chunksR_ok_append LinRQSC111.ok (chunksR_ok_append LinRQSC112.ok (chunksR_ok_append LinRQSC113.ok (chunksR_ok_append LinRQSC114.ok (chunksR_ok_append LinRQSC115.ok (chunksR_ok_append LinRQSC116.ok (chunksR_ok_append LinRQSC117.ok (chunksR_ok_append LinRQSC118.ok (chunksR_ok_append LinRQSC119.ok (chunksR_ok_append LinRQSC120.ok (chunksR_ok_append LinRQSC121.ok (chunksR_ok_append LinRQSC122.ok (chunksR_ok_append LinRQSC123.ok (chunksR_ok_append LinRQSC124.ok (chunksR_ok_append LinRQSC125.ok (chunksR_ok_append LinRQSC126.ok (LinRQSC127.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG3
end L5S4
end LRSpectrumFull

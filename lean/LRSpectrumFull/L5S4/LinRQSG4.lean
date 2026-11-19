/-
# L5S4.LinRQSG4 : node S group 4 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC128
import LRSpectrumFull.L5S4.LinRQSC129
import LRSpectrumFull.L5S4.LinRQSC130
import LRSpectrumFull.L5S4.LinRQSC131
import LRSpectrumFull.L5S4.LinRQSC132
import LRSpectrumFull.L5S4.LinRQSC133
import LRSpectrumFull.L5S4.LinRQSC134
import LRSpectrumFull.L5S4.LinRQSC135
import LRSpectrumFull.L5S4.LinRQSC136
import LRSpectrumFull.L5S4.LinRQSC137
import LRSpectrumFull.L5S4.LinRQSC138
import LRSpectrumFull.L5S4.LinRQSC139
import LRSpectrumFull.L5S4.LinRQSC140
import LRSpectrumFull.L5S4.LinRQSC141
import LRSpectrumFull.L5S4.LinRQSC142
import LRSpectrumFull.L5S4.LinRQSC143
import LRSpectrumFull.L5S4.LinRQSC144
import LRSpectrumFull.L5S4.LinRQSC145
import LRSpectrumFull.L5S4.LinRQSC146
import LRSpectrumFull.L5S4.LinRQSC147
import LRSpectrumFull.L5S4.LinRQSC148
import LRSpectrumFull.L5S4.LinRQSC149
import LRSpectrumFull.L5S4.LinRQSC150
import LRSpectrumFull.L5S4.LinRQSC151
import LRSpectrumFull.L5S4.LinRQSC152
import LRSpectrumFull.L5S4.LinRQSC153
import LRSpectrumFull.L5S4.LinRQSC154
import LRSpectrumFull.L5S4.LinRQSC155
import LRSpectrumFull.L5S4.LinRQSC156
import LRSpectrumFull.L5S4.LinRQSC157
import LRSpectrumFull.L5S4.LinRQSC158
import LRSpectrumFull.L5S4.LinRQSC159

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG4

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC128.blobs ++ (LinRQSC129.blobs ++ (LinRQSC130.blobs ++ (LinRQSC131.blobs ++ (LinRQSC132.blobs ++ (LinRQSC133.blobs ++ (LinRQSC134.blobs ++ (LinRQSC135.blobs ++ (LinRQSC136.blobs ++ (LinRQSC137.blobs ++ (LinRQSC138.blobs ++ (LinRQSC139.blobs ++ (LinRQSC140.blobs ++ (LinRQSC141.blobs ++ (LinRQSC142.blobs ++ (LinRQSC143.blobs ++ (LinRQSC144.blobs ++ (LinRQSC145.blobs ++ (LinRQSC146.blobs ++ (LinRQSC147.blobs ++ (LinRQSC148.blobs ++ (LinRQSC149.blobs ++ (LinRQSC150.blobs ++ (LinRQSC151.blobs ++ (LinRQSC152.blobs ++ (LinRQSC153.blobs ++ (LinRQSC154.blobs ++ (LinRQSC155.blobs ++ (LinRQSC156.blobs ++ (LinRQSC157.blobs ++ (LinRQSC158.blobs ++ (LinRQSC159.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC128.ok (chunksR_ok_append LinRQSC129.ok (chunksR_ok_append LinRQSC130.ok (chunksR_ok_append LinRQSC131.ok (chunksR_ok_append LinRQSC132.ok (chunksR_ok_append LinRQSC133.ok (chunksR_ok_append LinRQSC134.ok (chunksR_ok_append LinRQSC135.ok (chunksR_ok_append LinRQSC136.ok (chunksR_ok_append LinRQSC137.ok (chunksR_ok_append LinRQSC138.ok (chunksR_ok_append LinRQSC139.ok (chunksR_ok_append LinRQSC140.ok (chunksR_ok_append LinRQSC141.ok (chunksR_ok_append LinRQSC142.ok (chunksR_ok_append LinRQSC143.ok (chunksR_ok_append LinRQSC144.ok (chunksR_ok_append LinRQSC145.ok (chunksR_ok_append LinRQSC146.ok (chunksR_ok_append LinRQSC147.ok (chunksR_ok_append LinRQSC148.ok (chunksR_ok_append LinRQSC149.ok (chunksR_ok_append LinRQSC150.ok (chunksR_ok_append LinRQSC151.ok (chunksR_ok_append LinRQSC152.ok (chunksR_ok_append LinRQSC153.ok (chunksR_ok_append LinRQSC154.ok (chunksR_ok_append LinRQSC155.ok (chunksR_ok_append LinRQSC156.ok (chunksR_ok_append LinRQSC157.ok (chunksR_ok_append LinRQSC158.ok (LinRQSC159.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG4
end L5S4
end LRSpectrumFull

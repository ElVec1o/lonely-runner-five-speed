/-
# L5S4.LinRQSG5 : node S group 5 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC160
import LRSpectrumFull.L5S4.LinRQSC161
import LRSpectrumFull.L5S4.LinRQSC162
import LRSpectrumFull.L5S4.LinRQSC163
import LRSpectrumFull.L5S4.LinRQSC164
import LRSpectrumFull.L5S4.LinRQSC165
import LRSpectrumFull.L5S4.LinRQSC166
import LRSpectrumFull.L5S4.LinRQSC167
import LRSpectrumFull.L5S4.LinRQSC168
import LRSpectrumFull.L5S4.LinRQSC169
import LRSpectrumFull.L5S4.LinRQSC170
import LRSpectrumFull.L5S4.LinRQSC171
import LRSpectrumFull.L5S4.LinRQSC172
import LRSpectrumFull.L5S4.LinRQSC173
import LRSpectrumFull.L5S4.LinRQSC174
import LRSpectrumFull.L5S4.LinRQSC175
import LRSpectrumFull.L5S4.LinRQSC176
import LRSpectrumFull.L5S4.LinRQSC177
import LRSpectrumFull.L5S4.LinRQSC178
import LRSpectrumFull.L5S4.LinRQSC179
import LRSpectrumFull.L5S4.LinRQSC180
import LRSpectrumFull.L5S4.LinRQSC181
import LRSpectrumFull.L5S4.LinRQSC182
import LRSpectrumFull.L5S4.LinRQSC183
import LRSpectrumFull.L5S4.LinRQSC184
import LRSpectrumFull.L5S4.LinRQSC185
import LRSpectrumFull.L5S4.LinRQSC186
import LRSpectrumFull.L5S4.LinRQSC187
import LRSpectrumFull.L5S4.LinRQSC188
import LRSpectrumFull.L5S4.LinRQSC189
import LRSpectrumFull.L5S4.LinRQSC190
import LRSpectrumFull.L5S4.LinRQSC191

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG5

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC160.blobs ++ (LinRQSC161.blobs ++ (LinRQSC162.blobs ++ (LinRQSC163.blobs ++ (LinRQSC164.blobs ++ (LinRQSC165.blobs ++ (LinRQSC166.blobs ++ (LinRQSC167.blobs ++ (LinRQSC168.blobs ++ (LinRQSC169.blobs ++ (LinRQSC170.blobs ++ (LinRQSC171.blobs ++ (LinRQSC172.blobs ++ (LinRQSC173.blobs ++ (LinRQSC174.blobs ++ (LinRQSC175.blobs ++ (LinRQSC176.blobs ++ (LinRQSC177.blobs ++ (LinRQSC178.blobs ++ (LinRQSC179.blobs ++ (LinRQSC180.blobs ++ (LinRQSC181.blobs ++ (LinRQSC182.blobs ++ (LinRQSC183.blobs ++ (LinRQSC184.blobs ++ (LinRQSC185.blobs ++ (LinRQSC186.blobs ++ (LinRQSC187.blobs ++ (LinRQSC188.blobs ++ (LinRQSC189.blobs ++ (LinRQSC190.blobs ++ (LinRQSC191.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC160.ok (chunksR_ok_append LinRQSC161.ok (chunksR_ok_append LinRQSC162.ok (chunksR_ok_append LinRQSC163.ok (chunksR_ok_append LinRQSC164.ok (chunksR_ok_append LinRQSC165.ok (chunksR_ok_append LinRQSC166.ok (chunksR_ok_append LinRQSC167.ok (chunksR_ok_append LinRQSC168.ok (chunksR_ok_append LinRQSC169.ok (chunksR_ok_append LinRQSC170.ok (chunksR_ok_append LinRQSC171.ok (chunksR_ok_append LinRQSC172.ok (chunksR_ok_append LinRQSC173.ok (chunksR_ok_append LinRQSC174.ok (chunksR_ok_append LinRQSC175.ok (chunksR_ok_append LinRQSC176.ok (chunksR_ok_append LinRQSC177.ok (chunksR_ok_append LinRQSC178.ok (chunksR_ok_append LinRQSC179.ok (chunksR_ok_append LinRQSC180.ok (chunksR_ok_append LinRQSC181.ok (chunksR_ok_append LinRQSC182.ok (chunksR_ok_append LinRQSC183.ok (chunksR_ok_append LinRQSC184.ok (chunksR_ok_append LinRQSC185.ok (chunksR_ok_append LinRQSC186.ok (chunksR_ok_append LinRQSC187.ok (chunksR_ok_append LinRQSC188.ok (chunksR_ok_append LinRQSC189.ok (chunksR_ok_append LinRQSC190.ok (LinRQSC191.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG5
end L5S4
end LRSpectrumFull

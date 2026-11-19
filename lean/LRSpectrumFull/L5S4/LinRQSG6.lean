/-
# L5S4.LinRQSG6 : node S group 6 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC192
import LRSpectrumFull.L5S4.LinRQSC193
import LRSpectrumFull.L5S4.LinRQSC194
import LRSpectrumFull.L5S4.LinRQSC195
import LRSpectrumFull.L5S4.LinRQSC196
import LRSpectrumFull.L5S4.LinRQSC197
import LRSpectrumFull.L5S4.LinRQSC198
import LRSpectrumFull.L5S4.LinRQSC199
import LRSpectrumFull.L5S4.LinRQSC200
import LRSpectrumFull.L5S4.LinRQSC201
import LRSpectrumFull.L5S4.LinRQSC202
import LRSpectrumFull.L5S4.LinRQSC203
import LRSpectrumFull.L5S4.LinRQSC204
import LRSpectrumFull.L5S4.LinRQSC205
import LRSpectrumFull.L5S4.LinRQSC206
import LRSpectrumFull.L5S4.LinRQSC207
import LRSpectrumFull.L5S4.LinRQSC208
import LRSpectrumFull.L5S4.LinRQSC209
import LRSpectrumFull.L5S4.LinRQSC210
import LRSpectrumFull.L5S4.LinRQSC211
import LRSpectrumFull.L5S4.LinRQSC212
import LRSpectrumFull.L5S4.LinRQSC213
import LRSpectrumFull.L5S4.LinRQSC214
import LRSpectrumFull.L5S4.LinRQSC215
import LRSpectrumFull.L5S4.LinRQSC216
import LRSpectrumFull.L5S4.LinRQSC217
import LRSpectrumFull.L5S4.LinRQSC218
import LRSpectrumFull.L5S4.LinRQSC219
import LRSpectrumFull.L5S4.LinRQSC220
import LRSpectrumFull.L5S4.LinRQSC221
import LRSpectrumFull.L5S4.LinRQSC222
import LRSpectrumFull.L5S4.LinRQSC223

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG6

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC192.blobs ++ (LinRQSC193.blobs ++ (LinRQSC194.blobs ++ (LinRQSC195.blobs ++ (LinRQSC196.blobs ++ (LinRQSC197.blobs ++ (LinRQSC198.blobs ++ (LinRQSC199.blobs ++ (LinRQSC200.blobs ++ (LinRQSC201.blobs ++ (LinRQSC202.blobs ++ (LinRQSC203.blobs ++ (LinRQSC204.blobs ++ (LinRQSC205.blobs ++ (LinRQSC206.blobs ++ (LinRQSC207.blobs ++ (LinRQSC208.blobs ++ (LinRQSC209.blobs ++ (LinRQSC210.blobs ++ (LinRQSC211.blobs ++ (LinRQSC212.blobs ++ (LinRQSC213.blobs ++ (LinRQSC214.blobs ++ (LinRQSC215.blobs ++ (LinRQSC216.blobs ++ (LinRQSC217.blobs ++ (LinRQSC218.blobs ++ (LinRQSC219.blobs ++ (LinRQSC220.blobs ++ (LinRQSC221.blobs ++ (LinRQSC222.blobs ++ (LinRQSC223.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC192.ok (chunksR_ok_append LinRQSC193.ok (chunksR_ok_append LinRQSC194.ok (chunksR_ok_append LinRQSC195.ok (chunksR_ok_append LinRQSC196.ok (chunksR_ok_append LinRQSC197.ok (chunksR_ok_append LinRQSC198.ok (chunksR_ok_append LinRQSC199.ok (chunksR_ok_append LinRQSC200.ok (chunksR_ok_append LinRQSC201.ok (chunksR_ok_append LinRQSC202.ok (chunksR_ok_append LinRQSC203.ok (chunksR_ok_append LinRQSC204.ok (chunksR_ok_append LinRQSC205.ok (chunksR_ok_append LinRQSC206.ok (chunksR_ok_append LinRQSC207.ok (chunksR_ok_append LinRQSC208.ok (chunksR_ok_append LinRQSC209.ok (chunksR_ok_append LinRQSC210.ok (chunksR_ok_append LinRQSC211.ok (chunksR_ok_append LinRQSC212.ok (chunksR_ok_append LinRQSC213.ok (chunksR_ok_append LinRQSC214.ok (chunksR_ok_append LinRQSC215.ok (chunksR_ok_append LinRQSC216.ok (chunksR_ok_append LinRQSC217.ok (chunksR_ok_append LinRQSC218.ok (chunksR_ok_append LinRQSC219.ok (chunksR_ok_append LinRQSC220.ok (chunksR_ok_append LinRQSC221.ok (chunksR_ok_append LinRQSC222.ok (LinRQSC223.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG6
end L5S4
end LRSpectrumFull

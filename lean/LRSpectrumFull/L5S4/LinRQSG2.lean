/-
# L5S4.LinRQSG2 : node S group 2 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC64
import LRSpectrumFull.L5S4.LinRQSC65
import LRSpectrumFull.L5S4.LinRQSC66
import LRSpectrumFull.L5S4.LinRQSC67
import LRSpectrumFull.L5S4.LinRQSC68
import LRSpectrumFull.L5S4.LinRQSC69
import LRSpectrumFull.L5S4.LinRQSC70
import LRSpectrumFull.L5S4.LinRQSC71
import LRSpectrumFull.L5S4.LinRQSC72
import LRSpectrumFull.L5S4.LinRQSC73
import LRSpectrumFull.L5S4.LinRQSC74
import LRSpectrumFull.L5S4.LinRQSC75
import LRSpectrumFull.L5S4.LinRQSC76
import LRSpectrumFull.L5S4.LinRQSC77
import LRSpectrumFull.L5S4.LinRQSC78
import LRSpectrumFull.L5S4.LinRQSC79
import LRSpectrumFull.L5S4.LinRQSC80
import LRSpectrumFull.L5S4.LinRQSC81
import LRSpectrumFull.L5S4.LinRQSC82
import LRSpectrumFull.L5S4.LinRQSC83
import LRSpectrumFull.L5S4.LinRQSC84
import LRSpectrumFull.L5S4.LinRQSC85
import LRSpectrumFull.L5S4.LinRQSC86
import LRSpectrumFull.L5S4.LinRQSC87
import LRSpectrumFull.L5S4.LinRQSC88
import LRSpectrumFull.L5S4.LinRQSC89
import LRSpectrumFull.L5S4.LinRQSC90
import LRSpectrumFull.L5S4.LinRQSC91
import LRSpectrumFull.L5S4.LinRQSC92
import LRSpectrumFull.L5S4.LinRQSC93
import LRSpectrumFull.L5S4.LinRQSC94
import LRSpectrumFull.L5S4.LinRQSC95

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG2

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC64.blobs ++ (LinRQSC65.blobs ++ (LinRQSC66.blobs ++ (LinRQSC67.blobs ++ (LinRQSC68.blobs ++ (LinRQSC69.blobs ++ (LinRQSC70.blobs ++ (LinRQSC71.blobs ++ (LinRQSC72.blobs ++ (LinRQSC73.blobs ++ (LinRQSC74.blobs ++ (LinRQSC75.blobs ++ (LinRQSC76.blobs ++ (LinRQSC77.blobs ++ (LinRQSC78.blobs ++ (LinRQSC79.blobs ++ (LinRQSC80.blobs ++ (LinRQSC81.blobs ++ (LinRQSC82.blobs ++ (LinRQSC83.blobs ++ (LinRQSC84.blobs ++ (LinRQSC85.blobs ++ (LinRQSC86.blobs ++ (LinRQSC87.blobs ++ (LinRQSC88.blobs ++ (LinRQSC89.blobs ++ (LinRQSC90.blobs ++ (LinRQSC91.blobs ++ (LinRQSC92.blobs ++ (LinRQSC93.blobs ++ (LinRQSC94.blobs ++ (LinRQSC95.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC64.ok (chunksR_ok_append LinRQSC65.ok (chunksR_ok_append LinRQSC66.ok (chunksR_ok_append LinRQSC67.ok (chunksR_ok_append LinRQSC68.ok (chunksR_ok_append LinRQSC69.ok (chunksR_ok_append LinRQSC70.ok (chunksR_ok_append LinRQSC71.ok (chunksR_ok_append LinRQSC72.ok (chunksR_ok_append LinRQSC73.ok (chunksR_ok_append LinRQSC74.ok (chunksR_ok_append LinRQSC75.ok (chunksR_ok_append LinRQSC76.ok (chunksR_ok_append LinRQSC77.ok (chunksR_ok_append LinRQSC78.ok (chunksR_ok_append LinRQSC79.ok (chunksR_ok_append LinRQSC80.ok (chunksR_ok_append LinRQSC81.ok (chunksR_ok_append LinRQSC82.ok (chunksR_ok_append LinRQSC83.ok (chunksR_ok_append LinRQSC84.ok (chunksR_ok_append LinRQSC85.ok (chunksR_ok_append LinRQSC86.ok (chunksR_ok_append LinRQSC87.ok (chunksR_ok_append LinRQSC88.ok (chunksR_ok_append LinRQSC89.ok (chunksR_ok_append LinRQSC90.ok (chunksR_ok_append LinRQSC91.ok (chunksR_ok_append LinRQSC92.ok (chunksR_ok_append LinRQSC93.ok (chunksR_ok_append LinRQSC94.ok (LinRQSC95.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG2
end L5S4
end LRSpectrumFull

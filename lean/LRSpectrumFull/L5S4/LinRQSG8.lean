/-
# L5S4.LinRQSG8 : node S group 8 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC256
import LRSpectrumFull.L5S4.LinRQSC257
import LRSpectrumFull.L5S4.LinRQSC258
import LRSpectrumFull.L5S4.LinRQSC259
import LRSpectrumFull.L5S4.LinRQSC260
import LRSpectrumFull.L5S4.LinRQSC261
import LRSpectrumFull.L5S4.LinRQSC262
import LRSpectrumFull.L5S4.LinRQSC263
import LRSpectrumFull.L5S4.LinRQSC264
import LRSpectrumFull.L5S4.LinRQSC265
import LRSpectrumFull.L5S4.LinRQSC266
import LRSpectrumFull.L5S4.LinRQSC267
import LRSpectrumFull.L5S4.LinRQSC268
import LRSpectrumFull.L5S4.LinRQSC269
import LRSpectrumFull.L5S4.LinRQSC270
import LRSpectrumFull.L5S4.LinRQSC271
import LRSpectrumFull.L5S4.LinRQSC272
import LRSpectrumFull.L5S4.LinRQSC273
import LRSpectrumFull.L5S4.LinRQSC274
import LRSpectrumFull.L5S4.LinRQSC275
import LRSpectrumFull.L5S4.LinRQSC276
import LRSpectrumFull.L5S4.LinRQSC277
import LRSpectrumFull.L5S4.LinRQSC278
import LRSpectrumFull.L5S4.LinRQSC279
import LRSpectrumFull.L5S4.LinRQSC280
import LRSpectrumFull.L5S4.LinRQSC281
import LRSpectrumFull.L5S4.LinRQSC282
import LRSpectrumFull.L5S4.LinRQSC283
import LRSpectrumFull.L5S4.LinRQSC284
import LRSpectrumFull.L5S4.LinRQSC285
import LRSpectrumFull.L5S4.LinRQSC286
import LRSpectrumFull.L5S4.LinRQSC287

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG8

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC256.blobs ++ (LinRQSC257.blobs ++ (LinRQSC258.blobs ++ (LinRQSC259.blobs ++ (LinRQSC260.blobs ++ (LinRQSC261.blobs ++ (LinRQSC262.blobs ++ (LinRQSC263.blobs ++ (LinRQSC264.blobs ++ (LinRQSC265.blobs ++ (LinRQSC266.blobs ++ (LinRQSC267.blobs ++ (LinRQSC268.blobs ++ (LinRQSC269.blobs ++ (LinRQSC270.blobs ++ (LinRQSC271.blobs ++ (LinRQSC272.blobs ++ (LinRQSC273.blobs ++ (LinRQSC274.blobs ++ (LinRQSC275.blobs ++ (LinRQSC276.blobs ++ (LinRQSC277.blobs ++ (LinRQSC278.blobs ++ (LinRQSC279.blobs ++ (LinRQSC280.blobs ++ (LinRQSC281.blobs ++ (LinRQSC282.blobs ++ (LinRQSC283.blobs ++ (LinRQSC284.blobs ++ (LinRQSC285.blobs ++ (LinRQSC286.blobs ++ (LinRQSC287.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC256.ok (chunksR_ok_append LinRQSC257.ok (chunksR_ok_append LinRQSC258.ok (chunksR_ok_append LinRQSC259.ok (chunksR_ok_append LinRQSC260.ok (chunksR_ok_append LinRQSC261.ok (chunksR_ok_append LinRQSC262.ok (chunksR_ok_append LinRQSC263.ok (chunksR_ok_append LinRQSC264.ok (chunksR_ok_append LinRQSC265.ok (chunksR_ok_append LinRQSC266.ok (chunksR_ok_append LinRQSC267.ok (chunksR_ok_append LinRQSC268.ok (chunksR_ok_append LinRQSC269.ok (chunksR_ok_append LinRQSC270.ok (chunksR_ok_append LinRQSC271.ok (chunksR_ok_append LinRQSC272.ok (chunksR_ok_append LinRQSC273.ok (chunksR_ok_append LinRQSC274.ok (chunksR_ok_append LinRQSC275.ok (chunksR_ok_append LinRQSC276.ok (chunksR_ok_append LinRQSC277.ok (chunksR_ok_append LinRQSC278.ok (chunksR_ok_append LinRQSC279.ok (chunksR_ok_append LinRQSC280.ok (chunksR_ok_append LinRQSC281.ok (chunksR_ok_append LinRQSC282.ok (chunksR_ok_append LinRQSC283.ok (chunksR_ok_append LinRQSC284.ok (chunksR_ok_append LinRQSC285.ok (chunksR_ok_append LinRQSC286.ok (LinRQSC287.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG8
end L5S4
end LRSpectrumFull

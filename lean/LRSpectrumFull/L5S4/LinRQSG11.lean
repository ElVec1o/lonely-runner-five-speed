/-
# L5S4.LinRQSG11 : node S group 11 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC352
import LRSpectrumFull.L5S4.LinRQSC353
import LRSpectrumFull.L5S4.LinRQSC354
import LRSpectrumFull.L5S4.LinRQSC355
import LRSpectrumFull.L5S4.LinRQSC356
import LRSpectrumFull.L5S4.LinRQSC357
import LRSpectrumFull.L5S4.LinRQSC358
import LRSpectrumFull.L5S4.LinRQSC359
import LRSpectrumFull.L5S4.LinRQSC360
import LRSpectrumFull.L5S4.LinRQSC361
import LRSpectrumFull.L5S4.LinRQSC362
import LRSpectrumFull.L5S4.LinRQSC363
import LRSpectrumFull.L5S4.LinRQSC364
import LRSpectrumFull.L5S4.LinRQSC365
import LRSpectrumFull.L5S4.LinRQSC366
import LRSpectrumFull.L5S4.LinRQSC367
import LRSpectrumFull.L5S4.LinRQSC368
import LRSpectrumFull.L5S4.LinRQSC369
import LRSpectrumFull.L5S4.LinRQSC370
import LRSpectrumFull.L5S4.LinRQSC371
import LRSpectrumFull.L5S4.LinRQSC372
import LRSpectrumFull.L5S4.LinRQSC373
import LRSpectrumFull.L5S4.LinRQSC374
import LRSpectrumFull.L5S4.LinRQSC375
import LRSpectrumFull.L5S4.LinRQSC376
import LRSpectrumFull.L5S4.LinRQSC377
import LRSpectrumFull.L5S4.LinRQSC378
import LRSpectrumFull.L5S4.LinRQSC379
import LRSpectrumFull.L5S4.LinRQSC380
import LRSpectrumFull.L5S4.LinRQSC381
import LRSpectrumFull.L5S4.LinRQSC382
import LRSpectrumFull.L5S4.LinRQSC383

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG11

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC352.blobs ++ (LinRQSC353.blobs ++ (LinRQSC354.blobs ++ (LinRQSC355.blobs ++ (LinRQSC356.blobs ++ (LinRQSC357.blobs ++ (LinRQSC358.blobs ++ (LinRQSC359.blobs ++ (LinRQSC360.blobs ++ (LinRQSC361.blobs ++ (LinRQSC362.blobs ++ (LinRQSC363.blobs ++ (LinRQSC364.blobs ++ (LinRQSC365.blobs ++ (LinRQSC366.blobs ++ (LinRQSC367.blobs ++ (LinRQSC368.blobs ++ (LinRQSC369.blobs ++ (LinRQSC370.blobs ++ (LinRQSC371.blobs ++ (LinRQSC372.blobs ++ (LinRQSC373.blobs ++ (LinRQSC374.blobs ++ (LinRQSC375.blobs ++ (LinRQSC376.blobs ++ (LinRQSC377.blobs ++ (LinRQSC378.blobs ++ (LinRQSC379.blobs ++ (LinRQSC380.blobs ++ (LinRQSC381.blobs ++ (LinRQSC382.blobs ++ (LinRQSC383.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC352.ok (chunksR_ok_append LinRQSC353.ok (chunksR_ok_append LinRQSC354.ok (chunksR_ok_append LinRQSC355.ok (chunksR_ok_append LinRQSC356.ok (chunksR_ok_append LinRQSC357.ok (chunksR_ok_append LinRQSC358.ok (chunksR_ok_append LinRQSC359.ok (chunksR_ok_append LinRQSC360.ok (chunksR_ok_append LinRQSC361.ok (chunksR_ok_append LinRQSC362.ok (chunksR_ok_append LinRQSC363.ok (chunksR_ok_append LinRQSC364.ok (chunksR_ok_append LinRQSC365.ok (chunksR_ok_append LinRQSC366.ok (chunksR_ok_append LinRQSC367.ok (chunksR_ok_append LinRQSC368.ok (chunksR_ok_append LinRQSC369.ok (chunksR_ok_append LinRQSC370.ok (chunksR_ok_append LinRQSC371.ok (chunksR_ok_append LinRQSC372.ok (chunksR_ok_append LinRQSC373.ok (chunksR_ok_append LinRQSC374.ok (chunksR_ok_append LinRQSC375.ok (chunksR_ok_append LinRQSC376.ok (chunksR_ok_append LinRQSC377.ok (chunksR_ok_append LinRQSC378.ok (chunksR_ok_append LinRQSC379.ok (chunksR_ok_append LinRQSC380.ok (chunksR_ok_append LinRQSC381.ok (chunksR_ok_append LinRQSC382.ok (LinRQSC383.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG11
end L5S4
end LRSpectrumFull

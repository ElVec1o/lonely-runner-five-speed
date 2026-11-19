/-
# L5S4.LinRQSG10 : node S group 10 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC320
import LRSpectrumFull.L5S4.LinRQSC321
import LRSpectrumFull.L5S4.LinRQSC322
import LRSpectrumFull.L5S4.LinRQSC323
import LRSpectrumFull.L5S4.LinRQSC324
import LRSpectrumFull.L5S4.LinRQSC325
import LRSpectrumFull.L5S4.LinRQSC326
import LRSpectrumFull.L5S4.LinRQSC327
import LRSpectrumFull.L5S4.LinRQSC328
import LRSpectrumFull.L5S4.LinRQSC329
import LRSpectrumFull.L5S4.LinRQSC330
import LRSpectrumFull.L5S4.LinRQSC331
import LRSpectrumFull.L5S4.LinRQSC332
import LRSpectrumFull.L5S4.LinRQSC333
import LRSpectrumFull.L5S4.LinRQSC334
import LRSpectrumFull.L5S4.LinRQSC335
import LRSpectrumFull.L5S4.LinRQSC336
import LRSpectrumFull.L5S4.LinRQSC337
import LRSpectrumFull.L5S4.LinRQSC338
import LRSpectrumFull.L5S4.LinRQSC339
import LRSpectrumFull.L5S4.LinRQSC340
import LRSpectrumFull.L5S4.LinRQSC341
import LRSpectrumFull.L5S4.LinRQSC342
import LRSpectrumFull.L5S4.LinRQSC343
import LRSpectrumFull.L5S4.LinRQSC344
import LRSpectrumFull.L5S4.LinRQSC345
import LRSpectrumFull.L5S4.LinRQSC346
import LRSpectrumFull.L5S4.LinRQSC347
import LRSpectrumFull.L5S4.LinRQSC348
import LRSpectrumFull.L5S4.LinRQSC349
import LRSpectrumFull.L5S4.LinRQSC350
import LRSpectrumFull.L5S4.LinRQSC351

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG10

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC320.blobs ++ (LinRQSC321.blobs ++ (LinRQSC322.blobs ++ (LinRQSC323.blobs ++ (LinRQSC324.blobs ++ (LinRQSC325.blobs ++ (LinRQSC326.blobs ++ (LinRQSC327.blobs ++ (LinRQSC328.blobs ++ (LinRQSC329.blobs ++ (LinRQSC330.blobs ++ (LinRQSC331.blobs ++ (LinRQSC332.blobs ++ (LinRQSC333.blobs ++ (LinRQSC334.blobs ++ (LinRQSC335.blobs ++ (LinRQSC336.blobs ++ (LinRQSC337.blobs ++ (LinRQSC338.blobs ++ (LinRQSC339.blobs ++ (LinRQSC340.blobs ++ (LinRQSC341.blobs ++ (LinRQSC342.blobs ++ (LinRQSC343.blobs ++ (LinRQSC344.blobs ++ (LinRQSC345.blobs ++ (LinRQSC346.blobs ++ (LinRQSC347.blobs ++ (LinRQSC348.blobs ++ (LinRQSC349.blobs ++ (LinRQSC350.blobs ++ (LinRQSC351.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC320.ok (chunksR_ok_append LinRQSC321.ok (chunksR_ok_append LinRQSC322.ok (chunksR_ok_append LinRQSC323.ok (chunksR_ok_append LinRQSC324.ok (chunksR_ok_append LinRQSC325.ok (chunksR_ok_append LinRQSC326.ok (chunksR_ok_append LinRQSC327.ok (chunksR_ok_append LinRQSC328.ok (chunksR_ok_append LinRQSC329.ok (chunksR_ok_append LinRQSC330.ok (chunksR_ok_append LinRQSC331.ok (chunksR_ok_append LinRQSC332.ok (chunksR_ok_append LinRQSC333.ok (chunksR_ok_append LinRQSC334.ok (chunksR_ok_append LinRQSC335.ok (chunksR_ok_append LinRQSC336.ok (chunksR_ok_append LinRQSC337.ok (chunksR_ok_append LinRQSC338.ok (chunksR_ok_append LinRQSC339.ok (chunksR_ok_append LinRQSC340.ok (chunksR_ok_append LinRQSC341.ok (chunksR_ok_append LinRQSC342.ok (chunksR_ok_append LinRQSC343.ok (chunksR_ok_append LinRQSC344.ok (chunksR_ok_append LinRQSC345.ok (chunksR_ok_append LinRQSC346.ok (chunksR_ok_append LinRQSC347.ok (chunksR_ok_append LinRQSC348.ok (chunksR_ok_append LinRQSC349.ok (chunksR_ok_append LinRQSC350.ok (LinRQSC351.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG10
end L5S4
end LRSpectrumFull

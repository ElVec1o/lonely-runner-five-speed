/-
# L5S4.LinRQSG9 : node S group 9 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC288
import LRSpectrumFull.L5S4.LinRQSC289
import LRSpectrumFull.L5S4.LinRQSC290
import LRSpectrumFull.L5S4.LinRQSC291
import LRSpectrumFull.L5S4.LinRQSC292
import LRSpectrumFull.L5S4.LinRQSC293
import LRSpectrumFull.L5S4.LinRQSC294
import LRSpectrumFull.L5S4.LinRQSC295
import LRSpectrumFull.L5S4.LinRQSC296
import LRSpectrumFull.L5S4.LinRQSC297
import LRSpectrumFull.L5S4.LinRQSC298
import LRSpectrumFull.L5S4.LinRQSC299
import LRSpectrumFull.L5S4.LinRQSC300
import LRSpectrumFull.L5S4.LinRQSC301
import LRSpectrumFull.L5S4.LinRQSC302
import LRSpectrumFull.L5S4.LinRQSC303
import LRSpectrumFull.L5S4.LinRQSC304
import LRSpectrumFull.L5S4.LinRQSC305
import LRSpectrumFull.L5S4.LinRQSC306
import LRSpectrumFull.L5S4.LinRQSC307
import LRSpectrumFull.L5S4.LinRQSC308
import LRSpectrumFull.L5S4.LinRQSC309
import LRSpectrumFull.L5S4.LinRQSC310
import LRSpectrumFull.L5S4.LinRQSC311
import LRSpectrumFull.L5S4.LinRQSC312
import LRSpectrumFull.L5S4.LinRQSC313
import LRSpectrumFull.L5S4.LinRQSC314
import LRSpectrumFull.L5S4.LinRQSC315
import LRSpectrumFull.L5S4.LinRQSC316
import LRSpectrumFull.L5S4.LinRQSC317
import LRSpectrumFull.L5S4.LinRQSC318
import LRSpectrumFull.L5S4.LinRQSC319

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG9

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC288.blobs ++ (LinRQSC289.blobs ++ (LinRQSC290.blobs ++ (LinRQSC291.blobs ++ (LinRQSC292.blobs ++ (LinRQSC293.blobs ++ (LinRQSC294.blobs ++ (LinRQSC295.blobs ++ (LinRQSC296.blobs ++ (LinRQSC297.blobs ++ (LinRQSC298.blobs ++ (LinRQSC299.blobs ++ (LinRQSC300.blobs ++ (LinRQSC301.blobs ++ (LinRQSC302.blobs ++ (LinRQSC303.blobs ++ (LinRQSC304.blobs ++ (LinRQSC305.blobs ++ (LinRQSC306.blobs ++ (LinRQSC307.blobs ++ (LinRQSC308.blobs ++ (LinRQSC309.blobs ++ (LinRQSC310.blobs ++ (LinRQSC311.blobs ++ (LinRQSC312.blobs ++ (LinRQSC313.blobs ++ (LinRQSC314.blobs ++ (LinRQSC315.blobs ++ (LinRQSC316.blobs ++ (LinRQSC317.blobs ++ (LinRQSC318.blobs ++ (LinRQSC319.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC288.ok (chunksR_ok_append LinRQSC289.ok (chunksR_ok_append LinRQSC290.ok (chunksR_ok_append LinRQSC291.ok (chunksR_ok_append LinRQSC292.ok (chunksR_ok_append LinRQSC293.ok (chunksR_ok_append LinRQSC294.ok (chunksR_ok_append LinRQSC295.ok (chunksR_ok_append LinRQSC296.ok (chunksR_ok_append LinRQSC297.ok (chunksR_ok_append LinRQSC298.ok (chunksR_ok_append LinRQSC299.ok (chunksR_ok_append LinRQSC300.ok (chunksR_ok_append LinRQSC301.ok (chunksR_ok_append LinRQSC302.ok (chunksR_ok_append LinRQSC303.ok (chunksR_ok_append LinRQSC304.ok (chunksR_ok_append LinRQSC305.ok (chunksR_ok_append LinRQSC306.ok (chunksR_ok_append LinRQSC307.ok (chunksR_ok_append LinRQSC308.ok (chunksR_ok_append LinRQSC309.ok (chunksR_ok_append LinRQSC310.ok (chunksR_ok_append LinRQSC311.ok (chunksR_ok_append LinRQSC312.ok (chunksR_ok_append LinRQSC313.ok (chunksR_ok_append LinRQSC314.ok (chunksR_ok_append LinRQSC315.ok (chunksR_ok_append LinRQSC316.ok (chunksR_ok_append LinRQSC317.ok (chunksR_ok_append LinRQSC318.ok (LinRQSC319.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG9
end L5S4
end LRSpectrumFull

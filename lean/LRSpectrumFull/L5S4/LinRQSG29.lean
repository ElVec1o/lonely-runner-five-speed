/-
# L5S4.LinRQSG29 : node S group 29 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC928
import LRSpectrumFull.L5S4.LinRQSC929
import LRSpectrumFull.L5S4.LinRQSC930
import LRSpectrumFull.L5S4.LinRQSC931
import LRSpectrumFull.L5S4.LinRQSC932
import LRSpectrumFull.L5S4.LinRQSC933
import LRSpectrumFull.L5S4.LinRQSC934
import LRSpectrumFull.L5S4.LinRQSC935
import LRSpectrumFull.L5S4.LinRQSC936
import LRSpectrumFull.L5S4.LinRQSC937
import LRSpectrumFull.L5S4.LinRQSC938
import LRSpectrumFull.L5S4.LinRQSC939
import LRSpectrumFull.L5S4.LinRQSC940
import LRSpectrumFull.L5S4.LinRQSC941
import LRSpectrumFull.L5S4.LinRQSC942
import LRSpectrumFull.L5S4.LinRQSC943
import LRSpectrumFull.L5S4.LinRQSC944
import LRSpectrumFull.L5S4.LinRQSC945
import LRSpectrumFull.L5S4.LinRQSC946
import LRSpectrumFull.L5S4.LinRQSC947
import LRSpectrumFull.L5S4.LinRQSC948
import LRSpectrumFull.L5S4.LinRQSC949
import LRSpectrumFull.L5S4.LinRQSC950
import LRSpectrumFull.L5S4.LinRQSC951
import LRSpectrumFull.L5S4.LinRQSC952
import LRSpectrumFull.L5S4.LinRQSC953
import LRSpectrumFull.L5S4.LinRQSC954
import LRSpectrumFull.L5S4.LinRQSC955
import LRSpectrumFull.L5S4.LinRQSC956
import LRSpectrumFull.L5S4.LinRQSC957
import LRSpectrumFull.L5S4.LinRQSC958
import LRSpectrumFull.L5S4.LinRQSC959

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG29

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC928.blobs ++ (LinRQSC929.blobs ++ (LinRQSC930.blobs ++ (LinRQSC931.blobs ++ (LinRQSC932.blobs ++ (LinRQSC933.blobs ++ (LinRQSC934.blobs ++ (LinRQSC935.blobs ++ (LinRQSC936.blobs ++ (LinRQSC937.blobs ++ (LinRQSC938.blobs ++ (LinRQSC939.blobs ++ (LinRQSC940.blobs ++ (LinRQSC941.blobs ++ (LinRQSC942.blobs ++ (LinRQSC943.blobs ++ (LinRQSC944.blobs ++ (LinRQSC945.blobs ++ (LinRQSC946.blobs ++ (LinRQSC947.blobs ++ (LinRQSC948.blobs ++ (LinRQSC949.blobs ++ (LinRQSC950.blobs ++ (LinRQSC951.blobs ++ (LinRQSC952.blobs ++ (LinRQSC953.blobs ++ (LinRQSC954.blobs ++ (LinRQSC955.blobs ++ (LinRQSC956.blobs ++ (LinRQSC957.blobs ++ (LinRQSC958.blobs ++ (LinRQSC959.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC928.ok (chunksR_ok_append LinRQSC929.ok (chunksR_ok_append LinRQSC930.ok (chunksR_ok_append LinRQSC931.ok (chunksR_ok_append LinRQSC932.ok (chunksR_ok_append LinRQSC933.ok (chunksR_ok_append LinRQSC934.ok (chunksR_ok_append LinRQSC935.ok (chunksR_ok_append LinRQSC936.ok (chunksR_ok_append LinRQSC937.ok (chunksR_ok_append LinRQSC938.ok (chunksR_ok_append LinRQSC939.ok (chunksR_ok_append LinRQSC940.ok (chunksR_ok_append LinRQSC941.ok (chunksR_ok_append LinRQSC942.ok (chunksR_ok_append LinRQSC943.ok (chunksR_ok_append LinRQSC944.ok (chunksR_ok_append LinRQSC945.ok (chunksR_ok_append LinRQSC946.ok (chunksR_ok_append LinRQSC947.ok (chunksR_ok_append LinRQSC948.ok (chunksR_ok_append LinRQSC949.ok (chunksR_ok_append LinRQSC950.ok (chunksR_ok_append LinRQSC951.ok (chunksR_ok_append LinRQSC952.ok (chunksR_ok_append LinRQSC953.ok (chunksR_ok_append LinRQSC954.ok (chunksR_ok_append LinRQSC955.ok (chunksR_ok_append LinRQSC956.ok (chunksR_ok_append LinRQSC957.ok (chunksR_ok_append LinRQSC958.ok (LinRQSC959.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG29
end L5S4
end LRSpectrumFull

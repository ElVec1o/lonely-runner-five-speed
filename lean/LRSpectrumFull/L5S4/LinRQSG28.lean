/-
# L5S4.LinRQSG28 : node S group 28 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC896
import LRSpectrumFull.L5S4.LinRQSC897
import LRSpectrumFull.L5S4.LinRQSC898
import LRSpectrumFull.L5S4.LinRQSC899
import LRSpectrumFull.L5S4.LinRQSC900
import LRSpectrumFull.L5S4.LinRQSC901
import LRSpectrumFull.L5S4.LinRQSC902
import LRSpectrumFull.L5S4.LinRQSC903
import LRSpectrumFull.L5S4.LinRQSC904
import LRSpectrumFull.L5S4.LinRQSC905
import LRSpectrumFull.L5S4.LinRQSC906
import LRSpectrumFull.L5S4.LinRQSC907
import LRSpectrumFull.L5S4.LinRQSC908
import LRSpectrumFull.L5S4.LinRQSC909
import LRSpectrumFull.L5S4.LinRQSC910
import LRSpectrumFull.L5S4.LinRQSC911
import LRSpectrumFull.L5S4.LinRQSC912
import LRSpectrumFull.L5S4.LinRQSC913
import LRSpectrumFull.L5S4.LinRQSC914
import LRSpectrumFull.L5S4.LinRQSC915
import LRSpectrumFull.L5S4.LinRQSC916
import LRSpectrumFull.L5S4.LinRQSC917
import LRSpectrumFull.L5S4.LinRQSC918
import LRSpectrumFull.L5S4.LinRQSC919
import LRSpectrumFull.L5S4.LinRQSC920
import LRSpectrumFull.L5S4.LinRQSC921
import LRSpectrumFull.L5S4.LinRQSC922
import LRSpectrumFull.L5S4.LinRQSC923
import LRSpectrumFull.L5S4.LinRQSC924
import LRSpectrumFull.L5S4.LinRQSC925
import LRSpectrumFull.L5S4.LinRQSC926
import LRSpectrumFull.L5S4.LinRQSC927

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG28

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC896.blobs ++ (LinRQSC897.blobs ++ (LinRQSC898.blobs ++ (LinRQSC899.blobs ++ (LinRQSC900.blobs ++ (LinRQSC901.blobs ++ (LinRQSC902.blobs ++ (LinRQSC903.blobs ++ (LinRQSC904.blobs ++ (LinRQSC905.blobs ++ (LinRQSC906.blobs ++ (LinRQSC907.blobs ++ (LinRQSC908.blobs ++ (LinRQSC909.blobs ++ (LinRQSC910.blobs ++ (LinRQSC911.blobs ++ (LinRQSC912.blobs ++ (LinRQSC913.blobs ++ (LinRQSC914.blobs ++ (LinRQSC915.blobs ++ (LinRQSC916.blobs ++ (LinRQSC917.blobs ++ (LinRQSC918.blobs ++ (LinRQSC919.blobs ++ (LinRQSC920.blobs ++ (LinRQSC921.blobs ++ (LinRQSC922.blobs ++ (LinRQSC923.blobs ++ (LinRQSC924.blobs ++ (LinRQSC925.blobs ++ (LinRQSC926.blobs ++ (LinRQSC927.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC896.ok (chunksR_ok_append LinRQSC897.ok (chunksR_ok_append LinRQSC898.ok (chunksR_ok_append LinRQSC899.ok (chunksR_ok_append LinRQSC900.ok (chunksR_ok_append LinRQSC901.ok (chunksR_ok_append LinRQSC902.ok (chunksR_ok_append LinRQSC903.ok (chunksR_ok_append LinRQSC904.ok (chunksR_ok_append LinRQSC905.ok (chunksR_ok_append LinRQSC906.ok (chunksR_ok_append LinRQSC907.ok (chunksR_ok_append LinRQSC908.ok (chunksR_ok_append LinRQSC909.ok (chunksR_ok_append LinRQSC910.ok (chunksR_ok_append LinRQSC911.ok (chunksR_ok_append LinRQSC912.ok (chunksR_ok_append LinRQSC913.ok (chunksR_ok_append LinRQSC914.ok (chunksR_ok_append LinRQSC915.ok (chunksR_ok_append LinRQSC916.ok (chunksR_ok_append LinRQSC917.ok (chunksR_ok_append LinRQSC918.ok (chunksR_ok_append LinRQSC919.ok (chunksR_ok_append LinRQSC920.ok (chunksR_ok_append LinRQSC921.ok (chunksR_ok_append LinRQSC922.ok (chunksR_ok_append LinRQSC923.ok (chunksR_ok_append LinRQSC924.ok (chunksR_ok_append LinRQSC925.ok (chunksR_ok_append LinRQSC926.ok (LinRQSC927.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG28
end L5S4
end LRSpectrumFull

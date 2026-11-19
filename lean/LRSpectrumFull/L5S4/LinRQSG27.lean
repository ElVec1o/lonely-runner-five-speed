/-
# L5S4.LinRQSG27 : node S group 27 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC864
import LRSpectrumFull.L5S4.LinRQSC865
import LRSpectrumFull.L5S4.LinRQSC866
import LRSpectrumFull.L5S4.LinRQSC867
import LRSpectrumFull.L5S4.LinRQSC868
import LRSpectrumFull.L5S4.LinRQSC869
import LRSpectrumFull.L5S4.LinRQSC870
import LRSpectrumFull.L5S4.LinRQSC871
import LRSpectrumFull.L5S4.LinRQSC872
import LRSpectrumFull.L5S4.LinRQSC873
import LRSpectrumFull.L5S4.LinRQSC874
import LRSpectrumFull.L5S4.LinRQSC875
import LRSpectrumFull.L5S4.LinRQSC876
import LRSpectrumFull.L5S4.LinRQSC877
import LRSpectrumFull.L5S4.LinRQSC878
import LRSpectrumFull.L5S4.LinRQSC879
import LRSpectrumFull.L5S4.LinRQSC880
import LRSpectrumFull.L5S4.LinRQSC881
import LRSpectrumFull.L5S4.LinRQSC882
import LRSpectrumFull.L5S4.LinRQSC883
import LRSpectrumFull.L5S4.LinRQSC884
import LRSpectrumFull.L5S4.LinRQSC885
import LRSpectrumFull.L5S4.LinRQSC886
import LRSpectrumFull.L5S4.LinRQSC887
import LRSpectrumFull.L5S4.LinRQSC888
import LRSpectrumFull.L5S4.LinRQSC889
import LRSpectrumFull.L5S4.LinRQSC890
import LRSpectrumFull.L5S4.LinRQSC891
import LRSpectrumFull.L5S4.LinRQSC892
import LRSpectrumFull.L5S4.LinRQSC893
import LRSpectrumFull.L5S4.LinRQSC894
import LRSpectrumFull.L5S4.LinRQSC895

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG27

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC864.blobs ++ (LinRQSC865.blobs ++ (LinRQSC866.blobs ++ (LinRQSC867.blobs ++ (LinRQSC868.blobs ++ (LinRQSC869.blobs ++ (LinRQSC870.blobs ++ (LinRQSC871.blobs ++ (LinRQSC872.blobs ++ (LinRQSC873.blobs ++ (LinRQSC874.blobs ++ (LinRQSC875.blobs ++ (LinRQSC876.blobs ++ (LinRQSC877.blobs ++ (LinRQSC878.blobs ++ (LinRQSC879.blobs ++ (LinRQSC880.blobs ++ (LinRQSC881.blobs ++ (LinRQSC882.blobs ++ (LinRQSC883.blobs ++ (LinRQSC884.blobs ++ (LinRQSC885.blobs ++ (LinRQSC886.blobs ++ (LinRQSC887.blobs ++ (LinRQSC888.blobs ++ (LinRQSC889.blobs ++ (LinRQSC890.blobs ++ (LinRQSC891.blobs ++ (LinRQSC892.blobs ++ (LinRQSC893.blobs ++ (LinRQSC894.blobs ++ (LinRQSC895.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC864.ok (chunksR_ok_append LinRQSC865.ok (chunksR_ok_append LinRQSC866.ok (chunksR_ok_append LinRQSC867.ok (chunksR_ok_append LinRQSC868.ok (chunksR_ok_append LinRQSC869.ok (chunksR_ok_append LinRQSC870.ok (chunksR_ok_append LinRQSC871.ok (chunksR_ok_append LinRQSC872.ok (chunksR_ok_append LinRQSC873.ok (chunksR_ok_append LinRQSC874.ok (chunksR_ok_append LinRQSC875.ok (chunksR_ok_append LinRQSC876.ok (chunksR_ok_append LinRQSC877.ok (chunksR_ok_append LinRQSC878.ok (chunksR_ok_append LinRQSC879.ok (chunksR_ok_append LinRQSC880.ok (chunksR_ok_append LinRQSC881.ok (chunksR_ok_append LinRQSC882.ok (chunksR_ok_append LinRQSC883.ok (chunksR_ok_append LinRQSC884.ok (chunksR_ok_append LinRQSC885.ok (chunksR_ok_append LinRQSC886.ok (chunksR_ok_append LinRQSC887.ok (chunksR_ok_append LinRQSC888.ok (chunksR_ok_append LinRQSC889.ok (chunksR_ok_append LinRQSC890.ok (chunksR_ok_append LinRQSC891.ok (chunksR_ok_append LinRQSC892.ok (chunksR_ok_append LinRQSC893.ok (chunksR_ok_append LinRQSC894.ok (LinRQSC895.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG27
end L5S4
end LRSpectrumFull

/-
# L5S4.LinRQSG26 : node S group 26 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC832
import LRSpectrumFull.L5S4.LinRQSC833
import LRSpectrumFull.L5S4.LinRQSC834
import LRSpectrumFull.L5S4.LinRQSC835
import LRSpectrumFull.L5S4.LinRQSC836
import LRSpectrumFull.L5S4.LinRQSC837
import LRSpectrumFull.L5S4.LinRQSC838
import LRSpectrumFull.L5S4.LinRQSC839
import LRSpectrumFull.L5S4.LinRQSC840
import LRSpectrumFull.L5S4.LinRQSC841
import LRSpectrumFull.L5S4.LinRQSC842
import LRSpectrumFull.L5S4.LinRQSC843
import LRSpectrumFull.L5S4.LinRQSC844
import LRSpectrumFull.L5S4.LinRQSC845
import LRSpectrumFull.L5S4.LinRQSC846
import LRSpectrumFull.L5S4.LinRQSC847
import LRSpectrumFull.L5S4.LinRQSC848
import LRSpectrumFull.L5S4.LinRQSC849
import LRSpectrumFull.L5S4.LinRQSC850
import LRSpectrumFull.L5S4.LinRQSC851
import LRSpectrumFull.L5S4.LinRQSC852
import LRSpectrumFull.L5S4.LinRQSC853
import LRSpectrumFull.L5S4.LinRQSC854
import LRSpectrumFull.L5S4.LinRQSC855
import LRSpectrumFull.L5S4.LinRQSC856
import LRSpectrumFull.L5S4.LinRQSC857
import LRSpectrumFull.L5S4.LinRQSC858
import LRSpectrumFull.L5S4.LinRQSC859
import LRSpectrumFull.L5S4.LinRQSC860
import LRSpectrumFull.L5S4.LinRQSC861
import LRSpectrumFull.L5S4.LinRQSC862
import LRSpectrumFull.L5S4.LinRQSC863

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG26

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC832.blobs ++ (LinRQSC833.blobs ++ (LinRQSC834.blobs ++ (LinRQSC835.blobs ++ (LinRQSC836.blobs ++ (LinRQSC837.blobs ++ (LinRQSC838.blobs ++ (LinRQSC839.blobs ++ (LinRQSC840.blobs ++ (LinRQSC841.blobs ++ (LinRQSC842.blobs ++ (LinRQSC843.blobs ++ (LinRQSC844.blobs ++ (LinRQSC845.blobs ++ (LinRQSC846.blobs ++ (LinRQSC847.blobs ++ (LinRQSC848.blobs ++ (LinRQSC849.blobs ++ (LinRQSC850.blobs ++ (LinRQSC851.blobs ++ (LinRQSC852.blobs ++ (LinRQSC853.blobs ++ (LinRQSC854.blobs ++ (LinRQSC855.blobs ++ (LinRQSC856.blobs ++ (LinRQSC857.blobs ++ (LinRQSC858.blobs ++ (LinRQSC859.blobs ++ (LinRQSC860.blobs ++ (LinRQSC861.blobs ++ (LinRQSC862.blobs ++ (LinRQSC863.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC832.ok (chunksR_ok_append LinRQSC833.ok (chunksR_ok_append LinRQSC834.ok (chunksR_ok_append LinRQSC835.ok (chunksR_ok_append LinRQSC836.ok (chunksR_ok_append LinRQSC837.ok (chunksR_ok_append LinRQSC838.ok (chunksR_ok_append LinRQSC839.ok (chunksR_ok_append LinRQSC840.ok (chunksR_ok_append LinRQSC841.ok (chunksR_ok_append LinRQSC842.ok (chunksR_ok_append LinRQSC843.ok (chunksR_ok_append LinRQSC844.ok (chunksR_ok_append LinRQSC845.ok (chunksR_ok_append LinRQSC846.ok (chunksR_ok_append LinRQSC847.ok (chunksR_ok_append LinRQSC848.ok (chunksR_ok_append LinRQSC849.ok (chunksR_ok_append LinRQSC850.ok (chunksR_ok_append LinRQSC851.ok (chunksR_ok_append LinRQSC852.ok (chunksR_ok_append LinRQSC853.ok (chunksR_ok_append LinRQSC854.ok (chunksR_ok_append LinRQSC855.ok (chunksR_ok_append LinRQSC856.ok (chunksR_ok_append LinRQSC857.ok (chunksR_ok_append LinRQSC858.ok (chunksR_ok_append LinRQSC859.ok (chunksR_ok_append LinRQSC860.ok (chunksR_ok_append LinRQSC861.ok (chunksR_ok_append LinRQSC862.ok (LinRQSC863.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG26
end L5S4
end LRSpectrumFull

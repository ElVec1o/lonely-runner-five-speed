/-
# L5S4.LinRQSG24 : node S group 24 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC768
import LRSpectrumFull.L5S4.LinRQSC769
import LRSpectrumFull.L5S4.LinRQSC770
import LRSpectrumFull.L5S4.LinRQSC771
import LRSpectrumFull.L5S4.LinRQSC772
import LRSpectrumFull.L5S4.LinRQSC773
import LRSpectrumFull.L5S4.LinRQSC774
import LRSpectrumFull.L5S4.LinRQSC775
import LRSpectrumFull.L5S4.LinRQSC776
import LRSpectrumFull.L5S4.LinRQSC777
import LRSpectrumFull.L5S4.LinRQSC778
import LRSpectrumFull.L5S4.LinRQSC779
import LRSpectrumFull.L5S4.LinRQSC780
import LRSpectrumFull.L5S4.LinRQSC781
import LRSpectrumFull.L5S4.LinRQSC782
import LRSpectrumFull.L5S4.LinRQSC783
import LRSpectrumFull.L5S4.LinRQSC784
import LRSpectrumFull.L5S4.LinRQSC785
import LRSpectrumFull.L5S4.LinRQSC786
import LRSpectrumFull.L5S4.LinRQSC787
import LRSpectrumFull.L5S4.LinRQSC788
import LRSpectrumFull.L5S4.LinRQSC789
import LRSpectrumFull.L5S4.LinRQSC790
import LRSpectrumFull.L5S4.LinRQSC791
import LRSpectrumFull.L5S4.LinRQSC792
import LRSpectrumFull.L5S4.LinRQSC793
import LRSpectrumFull.L5S4.LinRQSC794
import LRSpectrumFull.L5S4.LinRQSC795
import LRSpectrumFull.L5S4.LinRQSC796
import LRSpectrumFull.L5S4.LinRQSC797
import LRSpectrumFull.L5S4.LinRQSC798
import LRSpectrumFull.L5S4.LinRQSC799

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG24

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC768.blobs ++ (LinRQSC769.blobs ++ (LinRQSC770.blobs ++ (LinRQSC771.blobs ++ (LinRQSC772.blobs ++ (LinRQSC773.blobs ++ (LinRQSC774.blobs ++ (LinRQSC775.blobs ++ (LinRQSC776.blobs ++ (LinRQSC777.blobs ++ (LinRQSC778.blobs ++ (LinRQSC779.blobs ++ (LinRQSC780.blobs ++ (LinRQSC781.blobs ++ (LinRQSC782.blobs ++ (LinRQSC783.blobs ++ (LinRQSC784.blobs ++ (LinRQSC785.blobs ++ (LinRQSC786.blobs ++ (LinRQSC787.blobs ++ (LinRQSC788.blobs ++ (LinRQSC789.blobs ++ (LinRQSC790.blobs ++ (LinRQSC791.blobs ++ (LinRQSC792.blobs ++ (LinRQSC793.blobs ++ (LinRQSC794.blobs ++ (LinRQSC795.blobs ++ (LinRQSC796.blobs ++ (LinRQSC797.blobs ++ (LinRQSC798.blobs ++ (LinRQSC799.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC768.ok (chunksR_ok_append LinRQSC769.ok (chunksR_ok_append LinRQSC770.ok (chunksR_ok_append LinRQSC771.ok (chunksR_ok_append LinRQSC772.ok (chunksR_ok_append LinRQSC773.ok (chunksR_ok_append LinRQSC774.ok (chunksR_ok_append LinRQSC775.ok (chunksR_ok_append LinRQSC776.ok (chunksR_ok_append LinRQSC777.ok (chunksR_ok_append LinRQSC778.ok (chunksR_ok_append LinRQSC779.ok (chunksR_ok_append LinRQSC780.ok (chunksR_ok_append LinRQSC781.ok (chunksR_ok_append LinRQSC782.ok (chunksR_ok_append LinRQSC783.ok (chunksR_ok_append LinRQSC784.ok (chunksR_ok_append LinRQSC785.ok (chunksR_ok_append LinRQSC786.ok (chunksR_ok_append LinRQSC787.ok (chunksR_ok_append LinRQSC788.ok (chunksR_ok_append LinRQSC789.ok (chunksR_ok_append LinRQSC790.ok (chunksR_ok_append LinRQSC791.ok (chunksR_ok_append LinRQSC792.ok (chunksR_ok_append LinRQSC793.ok (chunksR_ok_append LinRQSC794.ok (chunksR_ok_append LinRQSC795.ok (chunksR_ok_append LinRQSC796.ok (chunksR_ok_append LinRQSC797.ok (chunksR_ok_append LinRQSC798.ok (LinRQSC799.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG24
end L5S4
end LRSpectrumFull

/-
# L5S4.LinRQSG1 : node S group 1 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC32
import LRSpectrumFull.L5S4.LinRQSC33
import LRSpectrumFull.L5S4.LinRQSC34
import LRSpectrumFull.L5S4.LinRQSC35
import LRSpectrumFull.L5S4.LinRQSC36
import LRSpectrumFull.L5S4.LinRQSC37
import LRSpectrumFull.L5S4.LinRQSC38
import LRSpectrumFull.L5S4.LinRQSC39
import LRSpectrumFull.L5S4.LinRQSC40
import LRSpectrumFull.L5S4.LinRQSC41
import LRSpectrumFull.L5S4.LinRQSC42
import LRSpectrumFull.L5S4.LinRQSC43
import LRSpectrumFull.L5S4.LinRQSC44
import LRSpectrumFull.L5S4.LinRQSC45
import LRSpectrumFull.L5S4.LinRQSC46
import LRSpectrumFull.L5S4.LinRQSC47
import LRSpectrumFull.L5S4.LinRQSC48
import LRSpectrumFull.L5S4.LinRQSC49
import LRSpectrumFull.L5S4.LinRQSC50
import LRSpectrumFull.L5S4.LinRQSC51
import LRSpectrumFull.L5S4.LinRQSC52
import LRSpectrumFull.L5S4.LinRQSC53
import LRSpectrumFull.L5S4.LinRQSC54
import LRSpectrumFull.L5S4.LinRQSC55
import LRSpectrumFull.L5S4.LinRQSC56
import LRSpectrumFull.L5S4.LinRQSC57
import LRSpectrumFull.L5S4.LinRQSC58
import LRSpectrumFull.L5S4.LinRQSC59
import LRSpectrumFull.L5S4.LinRQSC60
import LRSpectrumFull.L5S4.LinRQSC61
import LRSpectrumFull.L5S4.LinRQSC62
import LRSpectrumFull.L5S4.LinRQSC63

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG1

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC32.blobs ++ (LinRQSC33.blobs ++ (LinRQSC34.blobs ++ (LinRQSC35.blobs ++ (LinRQSC36.blobs ++ (LinRQSC37.blobs ++ (LinRQSC38.blobs ++ (LinRQSC39.blobs ++ (LinRQSC40.blobs ++ (LinRQSC41.blobs ++ (LinRQSC42.blobs ++ (LinRQSC43.blobs ++ (LinRQSC44.blobs ++ (LinRQSC45.blobs ++ (LinRQSC46.blobs ++ (LinRQSC47.blobs ++ (LinRQSC48.blobs ++ (LinRQSC49.blobs ++ (LinRQSC50.blobs ++ (LinRQSC51.blobs ++ (LinRQSC52.blobs ++ (LinRQSC53.blobs ++ (LinRQSC54.blobs ++ (LinRQSC55.blobs ++ (LinRQSC56.blobs ++ (LinRQSC57.blobs ++ (LinRQSC58.blobs ++ (LinRQSC59.blobs ++ (LinRQSC60.blobs ++ (LinRQSC61.blobs ++ (LinRQSC62.blobs ++ (LinRQSC63.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC32.ok (chunksR_ok_append LinRQSC33.ok (chunksR_ok_append LinRQSC34.ok (chunksR_ok_append LinRQSC35.ok (chunksR_ok_append LinRQSC36.ok (chunksR_ok_append LinRQSC37.ok (chunksR_ok_append LinRQSC38.ok (chunksR_ok_append LinRQSC39.ok (chunksR_ok_append LinRQSC40.ok (chunksR_ok_append LinRQSC41.ok (chunksR_ok_append LinRQSC42.ok (chunksR_ok_append LinRQSC43.ok (chunksR_ok_append LinRQSC44.ok (chunksR_ok_append LinRQSC45.ok (chunksR_ok_append LinRQSC46.ok (chunksR_ok_append LinRQSC47.ok (chunksR_ok_append LinRQSC48.ok (chunksR_ok_append LinRQSC49.ok (chunksR_ok_append LinRQSC50.ok (chunksR_ok_append LinRQSC51.ok (chunksR_ok_append LinRQSC52.ok (chunksR_ok_append LinRQSC53.ok (chunksR_ok_append LinRQSC54.ok (chunksR_ok_append LinRQSC55.ok (chunksR_ok_append LinRQSC56.ok (chunksR_ok_append LinRQSC57.ok (chunksR_ok_append LinRQSC58.ok (chunksR_ok_append LinRQSC59.ok (chunksR_ok_append LinRQSC60.ok (chunksR_ok_append LinRQSC61.ok (chunksR_ok_append LinRQSC62.ok (LinRQSC63.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG1
end L5S4
end LRSpectrumFull

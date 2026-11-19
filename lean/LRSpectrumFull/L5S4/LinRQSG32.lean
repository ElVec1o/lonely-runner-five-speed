/-
# L5S4.LinRQSG32 : node S group 32 (29 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC1024
import LRSpectrumFull.L5S4.LinRQSC1025
import LRSpectrumFull.L5S4.LinRQSC1026
import LRSpectrumFull.L5S4.LinRQSC1027
import LRSpectrumFull.L5S4.LinRQSC1028
import LRSpectrumFull.L5S4.LinRQSC1029
import LRSpectrumFull.L5S4.LinRQSC1030
import LRSpectrumFull.L5S4.LinRQSC1031
import LRSpectrumFull.L5S4.LinRQSC1032
import LRSpectrumFull.L5S4.LinRQSC1033
import LRSpectrumFull.L5S4.LinRQSC1034
import LRSpectrumFull.L5S4.LinRQSC1035
import LRSpectrumFull.L5S4.LinRQSC1036
import LRSpectrumFull.L5S4.LinRQSC1037
import LRSpectrumFull.L5S4.LinRQSC1038
import LRSpectrumFull.L5S4.LinRQSC1039
import LRSpectrumFull.L5S4.LinRQSC1040
import LRSpectrumFull.L5S4.LinRQSC1041
import LRSpectrumFull.L5S4.LinRQSC1042
import LRSpectrumFull.L5S4.LinRQSC1043
import LRSpectrumFull.L5S4.LinRQSC1044
import LRSpectrumFull.L5S4.LinRQSC1045
import LRSpectrumFull.L5S4.LinRQSC1046
import LRSpectrumFull.L5S4.LinRQSC1047
import LRSpectrumFull.L5S4.LinRQSC1048
import LRSpectrumFull.L5S4.LinRQSC1049
import LRSpectrumFull.L5S4.LinRQSC1050
import LRSpectrumFull.L5S4.LinRQSC1051
import LRSpectrumFull.L5S4.LinRQSC1052

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG32

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC1024.blobs ++ (LinRQSC1025.blobs ++ (LinRQSC1026.blobs ++ (LinRQSC1027.blobs ++ (LinRQSC1028.blobs ++ (LinRQSC1029.blobs ++ (LinRQSC1030.blobs ++ (LinRQSC1031.blobs ++ (LinRQSC1032.blobs ++ (LinRQSC1033.blobs ++ (LinRQSC1034.blobs ++ (LinRQSC1035.blobs ++ (LinRQSC1036.blobs ++ (LinRQSC1037.blobs ++ (LinRQSC1038.blobs ++ (LinRQSC1039.blobs ++ (LinRQSC1040.blobs ++ (LinRQSC1041.blobs ++ (LinRQSC1042.blobs ++ (LinRQSC1043.blobs ++ (LinRQSC1044.blobs ++ (LinRQSC1045.blobs ++ (LinRQSC1046.blobs ++ (LinRQSC1047.blobs ++ (LinRQSC1048.blobs ++ (LinRQSC1049.blobs ++ (LinRQSC1050.blobs ++ (LinRQSC1051.blobs ++ (LinRQSC1052.blobs))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC1024.ok (chunksR_ok_append LinRQSC1025.ok (chunksR_ok_append LinRQSC1026.ok (chunksR_ok_append LinRQSC1027.ok (chunksR_ok_append LinRQSC1028.ok (chunksR_ok_append LinRQSC1029.ok (chunksR_ok_append LinRQSC1030.ok (chunksR_ok_append LinRQSC1031.ok (chunksR_ok_append LinRQSC1032.ok (chunksR_ok_append LinRQSC1033.ok (chunksR_ok_append LinRQSC1034.ok (chunksR_ok_append LinRQSC1035.ok (chunksR_ok_append LinRQSC1036.ok (chunksR_ok_append LinRQSC1037.ok (chunksR_ok_append LinRQSC1038.ok (chunksR_ok_append LinRQSC1039.ok (chunksR_ok_append LinRQSC1040.ok (chunksR_ok_append LinRQSC1041.ok (chunksR_ok_append LinRQSC1042.ok (chunksR_ok_append LinRQSC1043.ok (chunksR_ok_append LinRQSC1044.ok (chunksR_ok_append LinRQSC1045.ok (chunksR_ok_append LinRQSC1046.ok (chunksR_ok_append LinRQSC1047.ok (chunksR_ok_append LinRQSC1048.ok (chunksR_ok_append LinRQSC1049.ok (chunksR_ok_append LinRQSC1050.ok (chunksR_ok_append LinRQSC1051.ok (LinRQSC1052.ok))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG32
end L5S4
end LRSpectrumFull

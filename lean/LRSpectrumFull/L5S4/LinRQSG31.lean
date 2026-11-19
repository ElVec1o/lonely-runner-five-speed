/-
# L5S4.LinRQSG31 : node S group 31 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC992
import LRSpectrumFull.L5S4.LinRQSC993
import LRSpectrumFull.L5S4.LinRQSC994
import LRSpectrumFull.L5S4.LinRQSC995
import LRSpectrumFull.L5S4.LinRQSC996
import LRSpectrumFull.L5S4.LinRQSC997
import LRSpectrumFull.L5S4.LinRQSC998
import LRSpectrumFull.L5S4.LinRQSC999
import LRSpectrumFull.L5S4.LinRQSC1000
import LRSpectrumFull.L5S4.LinRQSC1001
import LRSpectrumFull.L5S4.LinRQSC1002
import LRSpectrumFull.L5S4.LinRQSC1003
import LRSpectrumFull.L5S4.LinRQSC1004
import LRSpectrumFull.L5S4.LinRQSC1005
import LRSpectrumFull.L5S4.LinRQSC1006
import LRSpectrumFull.L5S4.LinRQSC1007
import LRSpectrumFull.L5S4.LinRQSC1008
import LRSpectrumFull.L5S4.LinRQSC1009
import LRSpectrumFull.L5S4.LinRQSC1010
import LRSpectrumFull.L5S4.LinRQSC1011
import LRSpectrumFull.L5S4.LinRQSC1012
import LRSpectrumFull.L5S4.LinRQSC1013
import LRSpectrumFull.L5S4.LinRQSC1014
import LRSpectrumFull.L5S4.LinRQSC1015
import LRSpectrumFull.L5S4.LinRQSC1016
import LRSpectrumFull.L5S4.LinRQSC1017
import LRSpectrumFull.L5S4.LinRQSC1018
import LRSpectrumFull.L5S4.LinRQSC1019
import LRSpectrumFull.L5S4.LinRQSC1020
import LRSpectrumFull.L5S4.LinRQSC1021
import LRSpectrumFull.L5S4.LinRQSC1022
import LRSpectrumFull.L5S4.LinRQSC1023

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG31

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC992.blobs ++ (LinRQSC993.blobs ++ (LinRQSC994.blobs ++ (LinRQSC995.blobs ++ (LinRQSC996.blobs ++ (LinRQSC997.blobs ++ (LinRQSC998.blobs ++ (LinRQSC999.blobs ++ (LinRQSC1000.blobs ++ (LinRQSC1001.blobs ++ (LinRQSC1002.blobs ++ (LinRQSC1003.blobs ++ (LinRQSC1004.blobs ++ (LinRQSC1005.blobs ++ (LinRQSC1006.blobs ++ (LinRQSC1007.blobs ++ (LinRQSC1008.blobs ++ (LinRQSC1009.blobs ++ (LinRQSC1010.blobs ++ (LinRQSC1011.blobs ++ (LinRQSC1012.blobs ++ (LinRQSC1013.blobs ++ (LinRQSC1014.blobs ++ (LinRQSC1015.blobs ++ (LinRQSC1016.blobs ++ (LinRQSC1017.blobs ++ (LinRQSC1018.blobs ++ (LinRQSC1019.blobs ++ (LinRQSC1020.blobs ++ (LinRQSC1021.blobs ++ (LinRQSC1022.blobs ++ (LinRQSC1023.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC992.ok (chunksR_ok_append LinRQSC993.ok (chunksR_ok_append LinRQSC994.ok (chunksR_ok_append LinRQSC995.ok (chunksR_ok_append LinRQSC996.ok (chunksR_ok_append LinRQSC997.ok (chunksR_ok_append LinRQSC998.ok (chunksR_ok_append LinRQSC999.ok (chunksR_ok_append LinRQSC1000.ok (chunksR_ok_append LinRQSC1001.ok (chunksR_ok_append LinRQSC1002.ok (chunksR_ok_append LinRQSC1003.ok (chunksR_ok_append LinRQSC1004.ok (chunksR_ok_append LinRQSC1005.ok (chunksR_ok_append LinRQSC1006.ok (chunksR_ok_append LinRQSC1007.ok (chunksR_ok_append LinRQSC1008.ok (chunksR_ok_append LinRQSC1009.ok (chunksR_ok_append LinRQSC1010.ok (chunksR_ok_append LinRQSC1011.ok (chunksR_ok_append LinRQSC1012.ok (chunksR_ok_append LinRQSC1013.ok (chunksR_ok_append LinRQSC1014.ok (chunksR_ok_append LinRQSC1015.ok (chunksR_ok_append LinRQSC1016.ok (chunksR_ok_append LinRQSC1017.ok (chunksR_ok_append LinRQSC1018.ok (chunksR_ok_append LinRQSC1019.ok (chunksR_ok_append LinRQSC1020.ok (chunksR_ok_append LinRQSC1021.ok (chunksR_ok_append LinRQSC1022.ok (LinRQSC1023.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG31
end L5S4
end LRSpectrumFull

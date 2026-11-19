/-
# L5S4.LinRQSG30 : node S group 30 (32 chunks)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSC960
import LRSpectrumFull.L5S4.LinRQSC961
import LRSpectrumFull.L5S4.LinRQSC962
import LRSpectrumFull.L5S4.LinRQSC963
import LRSpectrumFull.L5S4.LinRQSC964
import LRSpectrumFull.L5S4.LinRQSC965
import LRSpectrumFull.L5S4.LinRQSC966
import LRSpectrumFull.L5S4.LinRQSC967
import LRSpectrumFull.L5S4.LinRQSC968
import LRSpectrumFull.L5S4.LinRQSC969
import LRSpectrumFull.L5S4.LinRQSC970
import LRSpectrumFull.L5S4.LinRQSC971
import LRSpectrumFull.L5S4.LinRQSC972
import LRSpectrumFull.L5S4.LinRQSC973
import LRSpectrumFull.L5S4.LinRQSC974
import LRSpectrumFull.L5S4.LinRQSC975
import LRSpectrumFull.L5S4.LinRQSC976
import LRSpectrumFull.L5S4.LinRQSC977
import LRSpectrumFull.L5S4.LinRQSC978
import LRSpectrumFull.L5S4.LinRQSC979
import LRSpectrumFull.L5S4.LinRQSC980
import LRSpectrumFull.L5S4.LinRQSC981
import LRSpectrumFull.L5S4.LinRQSC982
import LRSpectrumFull.L5S4.LinRQSC983
import LRSpectrumFull.L5S4.LinRQSC984
import LRSpectrumFull.L5S4.LinRQSC985
import LRSpectrumFull.L5S4.LinRQSC986
import LRSpectrumFull.L5S4.LinRQSC987
import LRSpectrumFull.L5S4.LinRQSC988
import LRSpectrumFull.L5S4.LinRQSC989
import LRSpectrumFull.L5S4.LinRQSC990
import LRSpectrumFull.L5S4.LinRQSC991

namespace LRSpectrumFull
namespace L5S4
namespace LinRQSG30

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSC960.blobs ++ (LinRQSC961.blobs ++ (LinRQSC962.blobs ++ (LinRQSC963.blobs ++ (LinRQSC964.blobs ++ (LinRQSC965.blobs ++ (LinRQSC966.blobs ++ (LinRQSC967.blobs ++ (LinRQSC968.blobs ++ (LinRQSC969.blobs ++ (LinRQSC970.blobs ++ (LinRQSC971.blobs ++ (LinRQSC972.blobs ++ (LinRQSC973.blobs ++ (LinRQSC974.blobs ++ (LinRQSC975.blobs ++ (LinRQSC976.blobs ++ (LinRQSC977.blobs ++ (LinRQSC978.blobs ++ (LinRQSC979.blobs ++ (LinRQSC980.blobs ++ (LinRQSC981.blobs ++ (LinRQSC982.blobs ++ (LinRQSC983.blobs ++ (LinRQSC984.blobs ++ (LinRQSC985.blobs ++ (LinRQSC986.blobs ++ (LinRQSC987.blobs ++ (LinRQSC988.blobs ++ (LinRQSC989.blobs ++ (LinRQSC990.blobs ++ (LinRQSC991.blobs)))))))))))))))))))))))))))))))

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact chunksR_ok_append LinRQSC960.ok (chunksR_ok_append LinRQSC961.ok (chunksR_ok_append LinRQSC962.ok (chunksR_ok_append LinRQSC963.ok (chunksR_ok_append LinRQSC964.ok (chunksR_ok_append LinRQSC965.ok (chunksR_ok_append LinRQSC966.ok (chunksR_ok_append LinRQSC967.ok (chunksR_ok_append LinRQSC968.ok (chunksR_ok_append LinRQSC969.ok (chunksR_ok_append LinRQSC970.ok (chunksR_ok_append LinRQSC971.ok (chunksR_ok_append LinRQSC972.ok (chunksR_ok_append LinRQSC973.ok (chunksR_ok_append LinRQSC974.ok (chunksR_ok_append LinRQSC975.ok (chunksR_ok_append LinRQSC976.ok (chunksR_ok_append LinRQSC977.ok (chunksR_ok_append LinRQSC978.ok (chunksR_ok_append LinRQSC979.ok (chunksR_ok_append LinRQSC980.ok (chunksR_ok_append LinRQSC981.ok (chunksR_ok_append LinRQSC982.ok (chunksR_ok_append LinRQSC983.ok (chunksR_ok_append LinRQSC984.ok (chunksR_ok_append LinRQSC985.ok (chunksR_ok_append LinRQSC986.ok (chunksR_ok_append LinRQSC987.ok (chunksR_ok_append LinRQSC988.ok (chunksR_ok_append LinRQSC989.ok (chunksR_ok_append LinRQSC990.ok (LinRQSC991.ok)))))))))))))))))))))))))))))))

#print axioms ok

end LinRQSG30
end L5S4
end LRSpectrumFull

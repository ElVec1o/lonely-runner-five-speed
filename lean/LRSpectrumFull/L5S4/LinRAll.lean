/-
# L5S4.LinRAll : all 81,436 classes: the lines certificate chunk theorems glued (`allBlobs` = blobs, `ok`)
-/
import LRSpectrumFull.L5S4.LinRGlue
import LRSpectrumFull.L5S4.LinRQSA

namespace LRSpectrumFull
namespace L5S4
namespace LinRAll

open LRSpectrumFull.L5S4.Lin

def blobs : List (Nat × Nat) := LinRQSA.blobs

theorem ok : (blobs.all fun p => classLinesR (dg p.1) p.2) = true := by
  unfold blobs
  exact LinRQSA.ok

#print axioms ok

end LinRAll
end L5S4
end LRSpectrumFull

import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 19 of 70: 2 pairs (a,b), 16206 tuples -/
theorem chunk45_19 : chunkP 45 nt45 ex45 [(3,7),(3,8)] = true := by decide +kernel

end L5W

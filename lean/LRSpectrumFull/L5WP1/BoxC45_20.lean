import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 20 of 70: 3 pairs (a,b), 19669 tuples -/
theorem chunk45_20 : chunkP 45 nt45 ex45 [(3,9),(3,10),(3,11)] = true := by decide +kernel

end L5W

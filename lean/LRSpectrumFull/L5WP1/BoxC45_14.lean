import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 14 of 70: 3 pairs (a,b), 19669 tuples -/
theorem chunk45_14 : chunkP 45 nt45 ex45 [(2,9),(2,10),(2,11)] = true := by decide +kernel

end L5W

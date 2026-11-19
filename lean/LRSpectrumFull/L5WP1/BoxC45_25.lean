import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 25 of 70: 2 pairs (a,b), 14910 tuples -/
theorem chunk45_25 : chunkP 45 nt45 ex45 [(4,8),(4,9)] = true := by decide +kernel

end L5W

import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 35 of 70: 2 pairs (a,b), 14910 tuples -/
theorem chunk45_35 : chunkP 45 nt45 ex45 [(6,8),(6,9)] = true := by decide +kernel

end L5W

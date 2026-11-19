import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 1 of 70: 1 pairs (a,b), 12341 tuples -/
theorem chunk45_1 : chunkP 45 nt45 ex45 [(1,2)] = true := by decide +kernel

end L5W

import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 10 of 70: 1 pairs (a,b), 11480 tuples -/
theorem chunk45_10 : chunkP 45 nt45 ex45 [(2,3)] = true := by decide +kernel

end L5W

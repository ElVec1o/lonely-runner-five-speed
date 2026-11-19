import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 24 of 70: 2 pairs (a,b), 17575 tuples -/
theorem chunk45_24 : chunkP 45 nt45 ex45 [(4,6),(4,7)] = true := by decide +kernel

end L5W

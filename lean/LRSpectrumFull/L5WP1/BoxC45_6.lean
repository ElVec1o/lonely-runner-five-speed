import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 6 of 70: 3 pairs (a,b), 19669 tuples -/
theorem chunk45_6 : chunkP 45 nt45 ex45 [(1,9),(1,10),(1,11)] = true := by decide +kernel

end L5W

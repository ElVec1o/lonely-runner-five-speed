import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 21 of 70: 4 pairs (a,b), 18971 tuples -/
theorem chunk45_21 : chunkP 45 nt45 ex45 [(3,12),(3,13),(3,14),(3,15)] = true := by decide +kernel

end L5W

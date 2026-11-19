import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 15 of 70: 4 pairs (a,b), 18971 tuples -/
theorem chunk45_15 : chunkP 45 nt45 ex45 [(2,12),(2,13),(2,14),(2,15)] = true := by decide +kernel

end L5W

import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 7 of 70: 4 pairs (a,b), 18971 tuples -/
theorem chunk45_7 : chunkP 45 nt45 ex45 [(1,12),(1,13),(1,14),(1,15)] = true := by decide +kernel

end L5W

import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 12 of 70: 2 pairs (a,b), 19019 tuples -/
theorem chunk45_12 : chunkP 45 nt45 ex45 [(2,5),(2,6)] = true := by decide +kernel

end L5W

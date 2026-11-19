import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 4 of 70: 2 pairs (a,b), 19019 tuples -/
theorem chunk45_4 : chunkP 45 nt45 ex45 [(1,5),(1,6)] = true := by decide +kernel

end L5W

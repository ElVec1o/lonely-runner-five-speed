import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 30 of 70: 2 pairs (a,b), 16206 tuples -/
theorem chunk45_30 : chunkP 45 nt45 ex45 [(5,7),(5,8)] = true := by decide +kernel

end L5W

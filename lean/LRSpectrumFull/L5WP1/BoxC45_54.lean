import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 54 of 70: 6 pairs (a,b), 18815 tuples -/
theorem chunk45_54 : chunkP 45 nt45 ex45 [(11,15),(11,16),(11,17),(11,18),(11,19),(11,20)] = true := by decide +kernel

end L5W

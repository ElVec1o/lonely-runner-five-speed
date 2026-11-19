import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 60 of 70: 6 pairs (a,b), 18815 tuples -/
theorem chunk45_60 : chunkP 45 nt45 ex45 [(14,15),(14,16),(14,17),(14,18),(14,19),(14,20)] = true := by decide +kernel

end L5W

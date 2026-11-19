import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 22 of 70: 7 pairs (a,b), 18550 tuples -/
theorem chunk45_22 : chunkP 45 nt45 ex45 [(3,16),(3,17),(3,18),(3,19),(3,20),(3,21),(3,22)] = true := by decide +kernel

end L5W

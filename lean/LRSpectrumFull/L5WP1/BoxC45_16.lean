import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 16 of 70: 7 pairs (a,b), 18550 tuples -/
theorem chunk45_16 : chunkP 45 nt45 ex45 [(2,16),(2,17),(2,18),(2,19),(2,20),(2,21),(2,22)] = true := by decide +kernel

end L5W

import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 8 of 70: 7 pairs (a,b), 18550 tuples -/
theorem chunk45_8 : chunkP 45 nt45 ex45 [(1,16),(1,17),(1,18),(1,19),(1,20),(1,21),(1,22)] = true := by decide +kernel

end L5W

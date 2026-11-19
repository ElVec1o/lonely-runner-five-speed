import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 33 of 70: 7 pairs (a,b), 18550 tuples -/
theorem chunk45_33 : chunkP 45 nt45 ex45 [(5,16),(5,17),(5,18),(5,19),(5,20),(5,21),(5,22)] = true := by decide +kernel

end L5W

import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 28 of 70: 10 pairs (a,b), 19875 tuples -/
theorem chunk45_28 : chunkP 45 nt45 ex45 [(4,17),(4,18),(4,19),(4,20),(4,21),(4,22),(4,23),(4,24),(4,25),(4,26)] = true := by decide +kernel

end L5W

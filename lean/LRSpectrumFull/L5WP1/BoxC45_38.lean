import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 38 of 70: 10 pairs (a,b), 19875 tuples -/
theorem chunk45_38 : chunkP 45 nt45 ex45 [(6,17),(6,18),(6,19),(6,20),(6,21),(6,22),(6,23),(6,24),(6,25),(6,26)] = true := by decide +kernel

end L5W

import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 49 of 70: 10 pairs (a,b), 19875 tuples -/
theorem chunk45_49 : chunkP 45 nt45 ex45 [(9,17),(9,18),(9,19),(9,20),(9,21),(9,22),(9,23),(9,24),(9,25),(9,26)] = true := by decide +kernel

end L5W

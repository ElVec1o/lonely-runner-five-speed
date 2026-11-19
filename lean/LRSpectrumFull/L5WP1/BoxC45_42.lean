import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 42 of 70: 10 pairs (a,b), 19875 tuples -/
theorem chunk45_42 : chunkP 45 nt45 ex45 [(7,17),(7,18),(7,19),(7,20),(7,21),(7,22),(7,23),(7,24),(7,25),(7,26)] = true := by decide +kernel

end L5W

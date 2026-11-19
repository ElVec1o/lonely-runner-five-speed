import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 56 of 70: 5 pairs (a,b), 18410 tuples -/
theorem chunk45_56 : chunkP 45 nt45 ex45 [(12,14),(12,15),(12,16),(12,17),(12,18)] = true := by decide +kernel

end L5W

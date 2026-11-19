import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 58 of 70: 5 pairs (a,b), 18410 tuples -/
theorem chunk45_58 : chunkP 45 nt45 ex45 [(13,14),(13,15),(13,16),(13,17),(13,18)] = true := by decide +kernel

end L5W

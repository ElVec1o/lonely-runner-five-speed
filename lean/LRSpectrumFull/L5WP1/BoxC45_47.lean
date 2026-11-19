import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 47 of 70: 3 pairs (a,b), 17985 tuples -/
theorem chunk45_47 : chunkP 45 nt45 ex45 [(9,10),(9,11),(9,12)] = true := by decide +kernel

end L5W

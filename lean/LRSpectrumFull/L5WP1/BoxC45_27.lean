import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 27 of 70: 4 pairs (a,b), 17169 tuples -/
theorem chunk45_27 : chunkP 45 nt45 ex45 [(4,13),(4,14),(4,15),(4,16)] = true := by decide +kernel

end L5W

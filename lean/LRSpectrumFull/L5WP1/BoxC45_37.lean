import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 37 of 70: 4 pairs (a,b), 17169 tuples -/
theorem chunk45_37 : chunkP 45 nt45 ex45 [(6,13),(6,14),(6,15),(6,16)] = true := by decide +kernel

end L5W

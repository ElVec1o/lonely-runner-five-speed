import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 41 of 70: 4 pairs (a,b), 17169 tuples -/
theorem chunk45_41 : chunkP 45 nt45 ex45 [(7,13),(7,14),(7,15),(7,16)] = true := by decide +kernel

end L5W

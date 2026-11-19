import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 51 of 70: 4 pairs (a,b), 17169 tuples -/
theorem chunk45_51 : chunkP 45 nt45 ex45 [(10,13),(10,14),(10,15),(10,16)] = true := by decide +kernel

end L5W

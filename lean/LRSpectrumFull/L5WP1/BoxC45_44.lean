import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 44 of 70: 3 pairs (a,b), 16400 tuples -/
theorem chunk45_44 : chunkP 45 nt45 ex45 [(8,11),(8,12),(8,13)] = true := by decide +kernel

end L5W

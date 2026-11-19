import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 45 of 70: 5 pairs (a,b), 18410 tuples -/
theorem chunk45_45 : chunkP 45 nt45 ex45 [(8,14),(8,15),(8,16),(8,17),(8,18)] = true := by decide +kernel

end L5W

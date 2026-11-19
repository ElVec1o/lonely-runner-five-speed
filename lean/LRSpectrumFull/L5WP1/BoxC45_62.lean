import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 62 of 70: 16 pairs (a,b), 19980 tuples -/
theorem chunk45_62 : chunkP 45 nt45 ex45 [(15,18),(15,19),(15,20),(15,21),(15,22),(15,23),(15,24),(15,25),(15,26),(15,27),(15,28),(15,29),(15,30),(15,31),(15,32),(15,33)] = true := by decide +kernel

end L5W

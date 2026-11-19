import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 29 of 70: 17 pairs (a,b), 13015 tuples -/
theorem chunk45_29 : chunkP 45 nt45 ex45 [(4,27),(4,28),(4,29),(4,30),(4,31),(4,32),(4,33),(4,34),(4,35),(4,36),(4,37),(4,38),(4,39),(4,40),(4,41),(4,42),(5,6)] = true := by decide +kernel

end L5W

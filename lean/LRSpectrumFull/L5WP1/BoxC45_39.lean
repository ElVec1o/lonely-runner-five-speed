import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 39 of 70: 18 pairs (a,b), 18786 tuples -/
theorem chunk45_39 : chunkP 45 nt45 ex45 [(6,27),(6,28),(6,29),(6,30),(6,31),(6,32),(6,33),(6,34),(6,35),(6,36),(6,37),(6,38),(6,39),(6,40),(6,41),(6,42),(7,8),(7,9)] = true := by decide +kernel

end L5W

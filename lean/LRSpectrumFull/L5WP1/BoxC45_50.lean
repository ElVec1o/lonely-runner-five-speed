import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 50 of 70: 18 pairs (a,b), 15316 tuples -/
theorem chunk45_50 : chunkP 45 nt45 ex45 [(9,27),(9,28),(9,29),(9,30),(9,31),(9,32),(9,33),(9,34),(9,35),(9,36),(9,37),(9,38),(9,39),(9,40),(9,41),(9,42),(10,11),(10,12)] = true := by decide +kernel

end L5W

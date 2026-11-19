import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 53 of 70: 19 pairs (a,b), 18787 tuples -/
theorem chunk45_53 : chunkP 45 nt45 ex45 [(10,27),(10,28),(10,29),(10,30),(10,31),(10,32),(10,33),(10,34),(10,35),(10,36),(10,37),(10,38),(10,39),(10,40),(10,41),(10,42),(11,12),(11,13),(11,14)] = true := by decide +kernel

end L5W

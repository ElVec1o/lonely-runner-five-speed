import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 9 of 70: 20 pairs (a,b), 8855 tuples -/
theorem chunk45_9 : chunkP 45 nt45 ex45 [(1,23),(1,24),(1,25),(1,26),(1,27),(1,28),(1,29),(1,30),(1,31),(1,32),(1,33),(1,34),(1,35),(1,36),(1,37),(1,38),(1,39),(1,40),(1,41),(1,42)] = true := by decide +kernel

end L5W

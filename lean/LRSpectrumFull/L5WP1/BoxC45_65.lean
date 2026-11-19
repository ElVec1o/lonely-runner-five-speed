import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 65 of 70: 26 pairs (a,b), 19659 tuples -/
theorem chunk45_65 : chunkP 45 nt45 ex45 [(17,25),(17,26),(17,27),(17,28),(17,29),(17,30),(17,31),(17,32),(17,33),(17,34),(17,35),(17,36),(17,37),(17,38),(17,39),(17,40),(17,41),(17,42),(18,19),(18,20),(18,21),(18,22),(18,23),(18,24),(18,25),(18,26)] = true := by decide +kernel

end L5W

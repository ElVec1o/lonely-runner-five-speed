import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 64 of 70: 24 pairs (a,b), 19335 tuples -/
theorem chunk45_64 : chunkP 45 nt45 ex45 [(16,26),(16,27),(16,28),(16,29),(16,30),(16,31),(16,32),(16,33),(16,34),(16,35),(16,36),(16,37),(16,38),(16,39),(16,40),(16,41),(16,42),(17,18),(17,19),(17,20),(17,21),(17,22),(17,23),(17,24)] = true := by decide +kernel

end L5W

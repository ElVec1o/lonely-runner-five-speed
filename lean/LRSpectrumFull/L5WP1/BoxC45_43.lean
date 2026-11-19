import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 43 of 70: 18 pairs (a,b), 17561 tuples -/
theorem chunk45_43 : chunkP 45 nt45 ex45 [(7,27),(7,28),(7,29),(7,30),(7,31),(7,32),(7,33),(7,34),(7,35),(7,36),(7,37),(7,38),(7,39),(7,40),(7,41),(7,42),(8,9),(8,10)] = true := by decide +kernel

end L5W

import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 63 of 70: 18 pairs (a,b), 19401 tuples -/
theorem chunk45_63 : chunkP 45 nt45 ex45 [(15,34),(15,35),(15,36),(15,37),(15,38),(15,39),(15,40),(15,41),(15,42),(16,17),(16,18),(16,19),(16,20),(16,21),(16,22),(16,23),(16,24),(16,25)] = true := by decide +kernel

end L5W

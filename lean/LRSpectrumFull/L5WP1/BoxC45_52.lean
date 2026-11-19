import LRSpectrumFull.L5WP1.BoxCore
import LRSpectrumFull.L5WP1.BoxData45

set_option Elab.async false
set_option maxHeartbeats 0

namespace L5W

/-- chunk 52 of 70: 10 pairs (a,b), 19875 tuples -/
theorem chunk45_52 : chunkP 45 nt45 ex45 [(10,17),(10,18),(10,19),(10,20),(10,21),(10,22),(10,23),(10,24),(10,25),(10,26)] = true := by decide +kernel

end L5W

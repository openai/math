import OAI.Optimization.LinearProgramming.Compression.ServiceState
import OAI.Optimization.LinearProgramming.Compression.ServiceTableOrder

/-! The physical generator table immediately after inspection of a requested minor. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open RAM OracleSpec

/-- The persistent state and all cursor values used by either possible continuation. -/
structure Inspected {d e n : ℕ} (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (J : Finset (NonzeroPairMinor D E)) (q : NonzeroPairMinor D E) (H : ℕ) (t : Memory ℚ) : Prop where
  persistent : Persistent D E J H t
  candidate : SlotAt D E q (slotBase n (J.card+1)) t
  rank : t.index 19 = GeneratorTable.rank q J.sort
  found : t.index 1 = (if q∈J then 1 else 0)
  base : t.index 14 = tableBase n
  count : t.index 17 = J.card
  stride : t.index 18 = GeneratorTable.stride n
  stop : t.index 20 = slotBase n J.card
  next : t.index 21 = slotBase n (J.card+1)
  dimension : t.index 22 = n

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.RAM.Code

/-! Persistent identity of a numerical proxy request. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Logical metadata slots retained by the cache, the mixed comparator, and
the dyadic bit driver throughout the rest of a request. -/
structure ProxyDriverMetadata {K : Type*} (N g member rank : ℕ) (m : Memory K) : Prop where
  dimension : m.index 102 = N
  generators : m.index 103 = g
  membership : m.index 104 = member
  position : m.index 105 = rank

end Compression
end LinearProgramming
end Optimization
end OAI

import OAI.Optimization.LinearProgramming.Compression.AllSmallCacheCall
import OAI.Optimization.LinearProgramming.Compression.SymbolicQueryTime

/-! The operation counts and scalar bit bounds used by the cached sign comparator. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

def cachedProxySignSteps (n fuel C : ℕ) : ℕ :=
  max (1+symbolicQuerySteps n fuel C+1) (1+allSmallCacheCallSteps n fuel C)

namespace SignWire

def isolatedCachedCost (n fuel C : ℕ) := 2*(cachedProxySignSteps n fuel C+5)+2

def numericalTagCost (n fuel C : ℕ) := (10*(n+1)+36) + isolatedCachedCost n fuel C

def wordComparatorBits (n fuel prec B : ℕ) :=
  max (symbolicQueryBits n fuel prec B) (fuel+4)

def wordComparatorTime (n fuel C : ℕ) :=
  16*((n+1)*(2*(fuel+1)+2)) + 13*(n+1) + numericalTagCost n fuel C + 19

end SignWire

end Compression
end LinearProgramming
end Optimization
end OAI

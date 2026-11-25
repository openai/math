import Mathlib.Data.Nat.Notation

/-! The operation budget for publishing a tagged rational of the given encoded length. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

def taggedReplyClock (k : ℕ) := 2*k*(16*k+17)+2*k*(16*k+18)+76*k+205

end Compression
end LinearProgramming
end Optimization
end OAI

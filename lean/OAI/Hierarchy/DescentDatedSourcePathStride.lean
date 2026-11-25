import Mathlib.Data.Nat.Log

namespace OAI
/-! # The dyadic host stride shared by the old-source path and local-rank columns -/
namespace Hierarchy.DescentDatedSourcePathDirectory

def stride (H : ℕ) := 2^Nat.clog 2 H

end Hierarchy.DescentDatedSourcePathDirectory

end OAI

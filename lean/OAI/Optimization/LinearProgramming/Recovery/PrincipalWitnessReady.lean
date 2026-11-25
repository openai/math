import OAI.Optimization.LinearProgramming.Recovery.PrincipalMath
import OAI.Optimization.LinearProgramming.Recovery.SlackRAM

/-! The final LP branch reads the retained input, the orientation flag, and the
normalized witness directly from the caller's register banks. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace Principal

open RAM

structure WitnessReady {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {m d : ℕ} (A : Matrix (Fin m) (Fin d) K) (b : Fin m→K) (raw atW cap : ℕ) (t : Memory K) : Prop where
  original : SlackRAM.InputAt t raw A b
  source : t.index 24=raw
  rows : t.index 28=m
  columns : t.index 29=d
  capacity : t.index 60=cap
  side : t.index 156=(ref A b).primal.toNat
  point : t.index 212=atW
  vector : ∀j : Fin (m+1),t.data (atW+j.val)=(ref A b).point j

end Principal
end Recovery
end LinearProgramming
end Optimization
end OAI

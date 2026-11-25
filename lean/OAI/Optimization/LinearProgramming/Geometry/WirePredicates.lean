import OAI.Optimization.LinearProgramming.Contract.AppOracleMachine
import OAI.Optimization.LinearProgramming.OracleSpec.Compression

/-! Public predicates on the scalar wire history and the sealed minor indices. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry

open RAM Contract OracleSpec

variable {r s n : ℕ}

/-- Every transmitted packet names an actual nonzero minor and every reply has one
of the two allowed tags in the public geometry calling convention. -/
def NamedTraffic (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (hist : Contract.History ℚ) : Prop :=
  ∀ w ∈ hist, ∃ u : MinorLog.Index D E, w.1 = (MinorLog.words u.val).map Nat.cast ∧ (w.2=[1] ∨ ∃ v, w.2=[0,v])

/-- Agreement is stated entirely on the sealed minor indices and the actual scalar
packets, so it also applies to callbacks maintaining their own compression state. -/
def AgreesOnReplies (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (h : Contract.History ℚ) (F : MinorLog.Index D E → ℚ) : Prop :=
  ∀ u v, ((MinorLog.words u.val).map Nat.cast,[0,v])∈h → F u=v

end Geometry
end LinearProgramming
end Optimization
end OAI

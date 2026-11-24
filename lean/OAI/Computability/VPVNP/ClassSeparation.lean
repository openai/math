import OAI.Computability.VPVNP.Separation
import OAI.Computability.VPVNP.Valiant.Project

/-! # Exact VP and VNP in the binary gate model -/

namespace OAI
namespace Computability
namespace VPVNP

namespace Standalone

universe u

/-- The two nonuniform classes differ over each field. -/
theorem vp_ne_vnp (F : Type u) [Field F] :
    (Valiant.Project.IsVP : Valiant.Project.Family F (fun n => Fin n × Bool) → Prop) ≠
      Valiant.Project.IsVNP := by
  intro same
  apply VPVNP.vp_ne_vnp F
  funext f
  apply propext
  exact (Valiant.Project.isVP_iff f).symm.trans ((Iff.of_eq (congrFun same f)).trans
    (Valiant.Project.isVNP_iff f))

end Standalone

end VPVNP
end Computability
end OAI

import OAI.Hierarchy.DescentNormalize

namespace OAI
/-! # The number of physical renamings on a measured normalization path -/
namespace Hierarchy.DescentSixParty.Normalize
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ}

noncomputable def nameCount {W : MarkedWorld F d P bits} (n : Normalize W) : ℕ := by
  induction n with
  | done _ => exact 0
  | split _ _ _ _ _ ih => exact ih
  | merge _ _ _ _ _ _ _ ih => exact ih
  | named _ _ _ _ ih => exact ih + 1

@[simp] theorem nameCount_append {W : MarkedWorld F d P bits} (n : Normalize W)
    (site : Equiv.Perm n.result.graph.Site) (edge : Equiv.Perm n.result.graph.Edge) :
    (n.appendNames site edge).nameCount=n.nameCount+1 := by
  induction n with
  | done=>rfl
  | split _ _ _ _ _ ih=>exact ih site edge
  | merge _ _ _ _ _ _ _ ih=>exact ih site edge
  | named _ _ _ _ ih=>exact congrArg (·+1) (ih site edge)


end Hierarchy.DescentSixParty.Normalize

end OAI

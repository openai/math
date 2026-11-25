import OAI.Hierarchy.DescentNormalize

namespace OAI
/-! # The cut quantum of the actual post-subround normalizer -/
namespace Hierarchy.DescentSixParty.Normalize
open Computability.BorderVNP.Crossing
variable {F P : Type} [Field F] {D : ℕ} {bits : P→ℕ}

/-- Every cable split occurring in this history uses the stated common grain. -/
def CutsEqual (q : ℕ) {W : MarkedWorld F D P bits} (n : Normalize W) : Prop := by
  induction n with
  | done _ => exact True
  | split _ u _ _ _ ih => exact u = q ∧ ih
  | merge _ _ _ _ _ _ _ ih => exact ih
  | named _ _ _ _ ih => exact ih

@[simp] theorem cutsEqual_appendNames {W : MarkedWorld F D P bits} (q : ℕ) (n : Normalize W)
    (s : Equiv.Perm n.result.graph.Site) (e : Equiv.Perm n.result.graph.Edge) :
    CutsEqual q (n.appendNames s e) ↔ CutsEqual q n := by
  induction n with
  | done=>rfl
  | split W u m fit tail ih=>exact and_congr_right fun _=>ih s e
  | merge W V key hub k g tail ih=>exact ih s e
  | named W a b tail ih=>exact ih s e


end Hierarchy.DescentSixParty.Normalize

end OAI

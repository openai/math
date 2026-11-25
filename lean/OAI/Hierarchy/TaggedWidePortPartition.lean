import Mathlib.Data.Fin.Basic

namespace OAI
/-! # Local partition of each physical half-chord into the original row intervals -/
namespace Hierarchy.Tagged.PassiveWindow

/-- The native local roles partition the bits of each actual half chord.
Distinct parallel rows need not remain in the same roles at the next date.
`base` is the native sum for earlier original row ordinals on that chord. -/
structure Parts (P I : Type*) (W : ℕ) (total : P→ℕ) where
  owner : I → Option P
  base : I→ℕ
  width : I→ℕ
  within : ∀i,width i ≤ W
  top : ∀i p,owner i=some p → base i+width i ≤ total p
  covers : ∀p (j : Fin (total p)),∃i,owner i=some p ∧ ∃a : Fin (width i),base i+a.val=j.val

end Hierarchy.Tagged.PassiveWindow

end OAI

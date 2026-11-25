import OAI.Computability.BorderVNP.PackedFrozenNodeProgram
import OAI.Computability.BorderVNP.PackedFrozenFreshCost

/-! # Gate bound for the four physical row writers of a shortening node -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FrozenTape.Node

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows CellAddressCircuit VPVNP.VerifierNetwork

variable {D m s old np n C C' d d' k k' w W : ℕ} [NeZero D] {K : Type*} [Field K]
variable (e : PaidIdentity K D m) (first : Fin D × Bool) (hm : 0 < m)
variable {A : Type} [Fintype A] (seed : A ↪ Fin n)
variable {σ R B : Type*} [Fintype σ] [Fintype R] [Fintype B] (carried : Frame σ (Pins R B d'))
variable (oldF : Fields s old np C d k w σ)
variable (newF : Fields (siteCapacity e s n) (edgeCapacity e old n) np C' d' k' w σ)
variable (cut : Frame σ ((Fin old × Band D) × CutCircuit.Result × Fin w))
variable (counts : Frame σ (A × Option (Fin e.count) × Fin w))
variable (work extent : Fin s → Fin w → σ) (occupied : Fin old → σ) (ports : Fin np → Bool)
variable (successor : Fin (edgeCapacity e old n) → σ)

local notation3 "V" => siteCapacity e s n
local notation3 "E" => edgeCapacity e old n

/-- Coefficient for all newly written immutable commands, fixed by the paid identity and terminal. -/
noncomputable def nodeCoefficient := 240000+freshCoefficient e first

/-- The actual node writer charges the carried block once, two instances of each shared clip
and count circuit, and a cubic word factor for every sparse sewn site and cable slot. -/
theorem frame_cubic (portSlots : np ≤ s)
    (widths : d ≤ W ∧ d' ≤ W ∧ w ≤ W ∧ Nat.clog 2 (12*(V+E+1)) ≤ W) :
    (frame e first hm seed carried oldF newF cut counts work extent occupied ports successor).size ≤
      carried.size+2*cut.size+2*counts.size+nodeCoefficient e first*(V+E+1)*(W+1)^3 := by
  have inherited := LayerRows.budget_cubic oldF e newF cut work extent portSlots widths
  have born := fresh_cubic e first seed newF cut counts portSlots widths.2
  exact (frame_size e first hm seed carried oldF newF cut counts work extent occupied ports successor).trans
    ((Nat.add_le_add_left (Nat.add_le_add inherited born) _).trans_eq (by unfold nodeCoefficient; ring))

end Packing.Inherited.FrozenTape.Node

end BorderVNP
end Computability
end OAI

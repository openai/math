import OAI.Hierarchy.DescentMatchedPairOrdinal
import OAI.Hierarchy.DescentPackLabels

namespace OAI
/-! # Matched row ordinals in the order of the occupied colonies -/

namespace Hierarchy.DescentPacking.PairRAM
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P : Type*} {bits : P→ℕ} (N : Network D P bits)
    {C : Type} [Fintype C] [DecidableEq C] (core : Finset N.Edge) (home : N.Site→C)
    (color : N.Site→Bool) (B : ℕ)
local notation "T" => nativeTraffic N core home
local notation "packAt" => fun c=>slabPacking T B (thinList home color c) (thickList home color c)
local notation "mass" => amount (live T)

def globalNumberBy (rank : C↪ℕ) := tableNumberBy mass (fun c=>(packAt c).decisions) rank

def groupStartBy (rank : C↪ℕ) (c : C) :=
  ProtocolRAMPortRanks.«prefix» (fun d=>Fintype.card (Pairs mass (packAt d).decisions)) rank c

theorem group_order_by (rank : C↪ℕ) (c : C) (e : Pairs mass (packAt c).decisions) :
    (globalNumberBy N core home color B rank ⟨c,e⟩).val=
      groupStartBy N core home color B rank c+(pairNumber mass (packAt c).decisions e).val := rfl

end
end Hierarchy.DescentPacking.PairRAM

end OAI

import OAI.Hierarchy.DescentBoundedWorldHistory
import OAI.Hierarchy.DescentWholeGrain
import OAI.Hierarchy.DescentOrderedResetRows

namespace OAI
/-! # Immutable retained inputs through the complete grain decomposition -/

namespace Hierarchy.DescentKernelHistory.BitDescription
open DescentSixParty MarkedWorld Computability.BorderVNP.Crossing DescentCableUnbundling
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} (W : MarkedWorld F d P bits)
variable (m : W.graph.Edge→ℕ) (q : ℕ) (cut : ∀e,W.graph.width e=m e*q)
local notation "N" => W.graph
local notation "M" => grains W m q

def grainBit (v : W.graph.Site) : BitRef (boundaryWidth N v)→BitRef (boundaryWidth (M) v)
  | ⟨.inr p,j⟩=>⟨.inr p,j⟩
  | ⟨.inl e,j⟩=>
    let t:=finProdFinEquiv.symm (Fin.cast (cut e.val) j)
    ⟨.inl ⟨⟨e.val,t.1⟩,e.property⟩,t.2⟩

def granular (B : BitDescription W) : BitDescription (W.granular m q cut) where
  Tag := B.Tag
  scalar := B.scalar
  recipe v := (B.recipe v).reroute (grainBit W m q cut v)
  correct := by
    apply (reads_iff_local ..).mpr
    intro v read pins
    refine (BitRecipe.reroute_eval (B.recipe v) B.scalar (grainBit W m q cut v)
      (localBit (grains W m q) read pins)).trans ?_
    let oldRead (e : Incident W.graph v) : Word (W.graph.width e.val) :=
      (splitWord (cut e.val)).symm (fun i => read ⟨⟨e.val,i⟩,e.property⟩)
    refine Eq.trans ?_ ((reads_iff_local W.graph B.scalar B.recipe W.tables).mp
      B.correct v oldRead pins)
    apply congrArg ((B.recipe v).value B.scalar)
    funext z
    rcases z with ⟨e|p,j⟩
    · rfl
    · rfl

end
end Hierarchy.DescentKernelHistory.BitDescription

end OAI

import OAI.Hierarchy.TaggedWideOriginalParts
import OAI.Hierarchy.TaggedWidePassiveGate

namespace OAI
/-! # Two actual original-row states in the fixed passive routing component -/

noncomputable section
namespace Hierarchy.Tagged.PassiveWindow
open AdaptiveProbe WireTelescope NamedAperture
open ThreeFlat Routing
open LinearAlgebra.SpectralBooks ChordGraph
open scoped Classical

variable {S n cap : ℕ} {A : Type} (ends : Fin n → Chord S) (bits : Fin n→ℕ) (s : Fin S)
    (room : ∀i,bits i ≤ cap) (slot : EndsAt ends bits s ↪ A)
    {total : Widths S} (shape : installedWidths ends bits=total)

theorem carried_reads (x : State total s) (data : A → Bits cap)
    (row : ∀i (u : Fin (bits i.val.val.1)),data (slot i) (u.castLE (room _))=
      rowBits ends bits (shape.symm ▸ x) ⟨(⟨i.val.val.1,u⟩,i.val.val.2),i.val.property⟩) :
    let c := carried ends bits s room slot shape
    ∀i p,c.owner i=some p→∀u : Fin (c.width i),data i (u.castLE (c.within i))=(x p).val.testBit (c.base i+u.val) := by
  cases shape
  intro c q p eqn u
  by_cases hit : ∃i,slot i=q
  · obtain ⟨i,rfl⟩ := hit
    have owner : byRow ends bits s i=p := by simpa [c,carried,Parts.expand,originalParts,slot.injective.extend_apply] using eqn
    subst p
    have ub : u.val<bits i.val.val.1 := by simpa [c,carried,Parts.expand,originalParts,slot.injective.extend_apply] using u.isLt
    let bit : Fin (bits i.val.val.1) := ⟨u.val,ub⟩
    have address : u.castLE (c.within (slot i)) = bit.castLE (room _) := Fin.ext rfl
    rw [address]
    simpa [c,carried,Parts.expand,originalParts,slot.injective.extend_apply,bit] using
      (row i bit).trans (data_at ends bits s x i bit)
  · have blank := Function.extend_apply' (fun i=>some (byRow ends bits s i)) (fun _=>none) q (by simpa [Set.mem_range] using hit)
    change Function.extend slot (fun i=>some (byRow ends bits s i)) (fun _=>none) q=some p at eqn
    rw [blank] at eqn
    contradiction

end Hierarchy.Tagged.PassiveWindow

end
end OAI

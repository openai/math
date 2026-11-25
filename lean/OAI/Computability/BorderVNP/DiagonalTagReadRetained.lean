import OAI.Computability.BorderVNP.DiagonalTagProgramRead
import OAI.Computability.BorderVNP.DiagonalSpecializedDenseStep

/-! # Pointwise tagged birth reads through a true retained crossing site -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Site.Lineage

open Crossing Shortening Shortening.CombiningStep Shortening.SeedIntervals Diagonal.CellEntries MvPolynomial
open private extendWires extendPorts from OAI.Computability.BorderVNP.PackedInheritedRoundValue
open scoped Classical

variable {D m ne nf np : ℕ} [NeZero D] {K E : Type} [Field K] [Field E] {Param Gadget : Type}
    (e : PaidIdentity K D m) (y : e.Entry → E)
    (hy : ∀ f : MvPolynomial e.Entry ℤ, eval₂Hom (Int.castRingHom K) e.entry f = 0 →
      eval₂Hom (Int.castRingHom E) y f = 0)
    {P : Type} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K) {A : Type} [Fintype A]
    (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A) (name : A → ℕ)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    (v : p.layout.Site) (oldID : p.layout.Edge ↪ Fin ne)
    (nextID : (output e p bin perm positive first q).layout.Edge ↪ Fin nf) (ports : P ↪ Fin np)

local notation3 "net" => (output e p bin perm positive first q).layout
local notation3 "cuts" => Layer.orderedCuts p oldID ports v e bin perm name positive first q nextID

/-- The lineage physically retained by the interval allocator, with its
birth checker and the real stable order of clipped cable and port words. -/
noncomputable def orderedLayer (s : Lineage (Inherited.incoming p.layout v)) :
    Lineage (Inherited.incoming net (.inl v)) :=
  ⟨s.birth,s.program.retain (Inherited.incoming net (.inl v)) cuts,
    orderedRetention e p bin perm name positive first q v oldID nextID ports s.retention s.size,rfl⟩

set_option maxHeartbeats 1500000 in
/-- Retaining a site preserves the exact birth work and occurrence counts
on every locally supplied successor cable and port word. The reference-field
layout is used also when the newly inserted factors are specialized to a
different characteristic. -/
theorem TagModel.orderedLayer (s : Lineage (Inherited.incoming p.layout v))
    (compatible : (Fin s.birth.work → Bool) → Prop) (tags : p.layout.Tables (Entry Param Gadget))
    (pos : e.Entry → Gadget) (number : Gadget ↪ ℕ)
    (old : TagModel p.layout oldID ports v s compatible tags number) :
    TagModel net nextID ports (.inl v) (orderedLayer e p bin perm name positive first q v oldID nextID ports s)
      compatible (roundTags ⟨p.layout,tags⟩ bin perm (e.specialize y hy) pos positive first q).table number := by
  intro z x
  let v' : (net).Site := .inl v
  let wires := extendWires net v' z
  let exterior := extendPorts net v' x
  have hz : (fun u : Incident net v' => wires u.val) = z := by
    funext u j
    exact dite_eq_left u.property
  have hx : (fun u : Attached net v' => exterior u.val) = x := by
    funext u j
    exact dite_eq_left u.property
  let source := oldWireWords e p bin perm positive first q wires v
  let outside := oldPortWords p exterior v
  have inputs := layerRead_inputs e p bin perm positive first q v oldID nextID ports wires exterior
  have tag := old_tagged_read e p bin perm positive first q tags pos wires exterior v
  change (roundTags ⟨p.layout,tags⟩ bin perm (e.specialize y hy) pos positive first q).table v'
    (fun u => wires u.val) (fun u => exterior u.val) = tags v source outside at tag
  change inputWords net nextID ports v' (fun u => wires u.val) (fun u => exterior u.val) ∘
    layerRead e p bin perm positive first q v oldID nextID ports = inputWords p.layout oldID ports v source outside at inputs
  rw [hz,hx] at inputs
  have localTag := (congrArg₂ (fun (a : ∀ u : Incident net v', Fin ((net).width u.val) → Bool)
    (b : ∀ u : Attached net v', Fin (bits u.val) → Bool) =>
      (roundTags ⟨p.layout,tags⟩ bin perm (e.specialize y hy) pos positive first q).table v' a b) hz hx).symm.trans tag
  have full := congrArg (fun word => s.retention.readInput (word ∘ Fin.cast s.size)) inputs
  exact (congrArg₂ (fun w t => Nonempty (TagRead s.birth w compatible t number)) full localTag).mpr (old source outside)

end Packing.Inherited.Site.Lineage

end BorderVNP
end Computability
end OAI

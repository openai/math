import OAI.Computability.BorderVNP.DiagonalTaggedProgramModels
import OAI.Computability.BorderVNP.PackedSubdivisionPrivatePrograms
import OAI.Computability.BorderVNP.DiagonalExternalSewEnriched

/-! # Tagged observations through the true endpoint subdivision and relay programs -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision

open Crossing Diagonal.CellEntries Diagonal.ExternalSew Site.Programs
open scoped Classical

variable {D ne nn np : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {Param Gadget : Type*}
  (N : Network D P bits) (route : N.WireRoutes) (oldID : N.Edge ↪ Fin ne)
  (newID : (N.subdivide route).Edge ↪ Fin nn) (portID : P ↪ Fin np) (prior : Site.Programs N)
  (tags : N.Tables (Entry Param Gadget)) (num : Gadget ↪ ℕ) (pred : N.Site → (ℕ → Bool) → Prop)

local notation "G" => N.subdivide route
local notation "next" => subdividePrivatePrograms N route oldID newID portID prior
local notation "carry" => carryPred (Retains.site (Retains.subdivide N route)) pred

/-- Retained sites read exactly their original source-first incidence inputs.
Every new relay has one possible work word and reports no scalar. Its unique
passing condition compares both physical adjacent hops, including width zero. -/
theorem subdivide_tagModels (h : TagModels N oldID portID prior tags num pred) :
    TagModels G newID portID next (N.subdivideTables route tags) num carry := by
  rintro (v | j) z x
  · have original := h v (oldWires N route v z) (oldPorts N route v x)
    have words := read_inputs N route v oldID newID portID z x
    let p := prior v
    have wordEq := congrArg (fun a => p.retention.readInput (a ∘ Fin.cast p.size)) words
    have condition : (fun g : Fin p.birth.work → Bool => carry (.inl v) (extendWork g)) =
        fun g => pred v (extendWork g) := funext fun g =>
      propext (carryPred_old (Retains.subdivide N route).site pred v (extendWork g))
    rw [original_table N route v z x tags]
    change Nonempty (Site.TagRead p.birth
      (p.retention.readInput ((inputWords G newID portID (.inl v) z x ∘ read N route v oldID newID portID) ∘ Fin.cast p.size))
      (fun g => carry (.inl v) (extendWork g)) _ num)
    rw [wordEq,condition]
    exact original
  · let site := relaySite N route newID portID j
    let input := inputWords G newID portID (.inr j) z x
    let test := z (leftHop N route j) = z (rightHop N route j)
    let tag : Entry Param Gadget := if test then 1 else 0
    change Nonempty (Site.TagRead site input (fun g => carry (.inr j) (extendWork g)) tag num)
    refine ⟨⟨Fin.elim0,[],carryPred_new _ _ (fun u e => by change Sum.inl u = Sum.inr j at e; cases e) _,?_,?_⟩⟩
    · intro g os _
      have uniq : g = (Fin.elim0 : Fin 0 → Bool) := funext fun i => Fin.elim0 i
      rw [relay_observe N route newID portID j]
      change (if (relayRecord N route newID portID j).Valid [] (Inherited.bits g
        (inputWords G newID portID (.inr j) z x)) then some [] else none) = some os ↔ _
      have valid := relay_valid_inputs N route newID portID j z x g
      split
      · rename_i ok
        have pass : test := valid.mp ok
        simp [tag,pass,uniq,eq_comm]
        exact fun _ => rfl
      · rename_i bad
        have fail : ¬test := fun h => bad (valid.mpr h)
        simp [tag,fail]
    · intro _ label
      by_cases pass : test <;> simp only [tag,pass,ite_true,ite_false,List.filterMap_nil,List.count_nil] <;> rfl

end Packing.Inherited.Subdivision

end BorderVNP
end Computability
end OAI

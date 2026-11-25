import OAI.Hierarchy.ProbeCoreWalks
import OAI.Hierarchy.TaggedWireRowGraph

namespace OAI
/-! # Recovering a commodity or a catalyst from an unoriented physical edge -/
namespace Hierarchy
open LinearAlgebra.SpectralBooks ChordGraph
namespace WireTelescope

theorem orderedChord_cases {K : ℕ} {a b c d : Fin K} {left : a≠b} {right : c≠d}
    (same : orderedChord a b left=orderedChord c d right) : (a=c ∧ b=d) ∨ (a=d ∧ b=c) := by
  have pair:=congrArg Subtype.val same
  by_cases first : a<b
  · by_cases second : c<d
    · exact Or.inl (by simpa [orderedChord,first,second] using pair)
    · exact Or.inr (by simpa [orderedChord,first,second] using pair)
  · by_cases second : c<d
    · exact Or.inr (by simpa [orderedChord,first,second,and_comm] using pair)
    · exact Or.inl (by simpa [orderedChord,first,second,and_comm] using pair)

/-- Keeping the side classes disjoint lets the sorted chord recover both
original oriented endpoints without a global ordering convention. -/
theorem ordered_row_injective {K : ℕ} {V I : Type*} (place : V ↪ Fin K) (endpoints : I→V×V)
    (distinct : Function.Injective endpoints) (sides : ∀i j,(endpoints i).1≠(endpoints j).2) :
    Function.Injective (fun i=>orderedChord (place (endpoints i).1) (place (endpoints i).2)
      (place.injective.ne (sides i i))) := by
  intro i j eqn
  rcases orderedChord_cases eqn with h|h
  · exact distinct (Prod.ext (place.injective h.1) (place.injective h.2))
  · exact False.elim (sides i j (place.injective h.1))
end WireTelescope

namespace ProbeStage.CoreBoard
open AdaptiveProbe WireTelescope
variable {h d k K : ℕ}

theorem commodity_input_ne_output (π : Equiv.Perm (Fin (2^h)))
    (i j : Commodity (Fin (2^h)) (Stages h d) k) : (commodityEnds π i).1≠(commodityEnds π j).2 := by
  rcases i with p|⟨⟨p,t⟩,l⟩ <;> rcases j with q|⟨⟨q,u⟩,m⟩ <;> simp [commodityEnds,inputCol,outputCol]

theorem commodity_ends_injective (π : Equiv.Perm (Fin (2^h))) :
    Function.Injective (commodityEnds (d:=d) (k:=k) π) := by
  rintro (p|⟨⟨p,t⟩,l⟩) (q|⟨⟨q,u⟩,m⟩) eqn
  · exact congrArg Sum.inl (Sum.inl.inj (congrArg (fun e : Site h d k×Site h d k=>e.1.1) eqn))
  · exact False.elim (Sum.inl_ne_inr (congrArg (fun e : Site h d k×Site h d k=>e.1.1) eqn))
  · exact False.elim (Sum.inr_ne_inl (congrArg (fun e : Site h d k×Site h d k=>e.1.1) eqn))
  · have sites:=Sum.inl.inj (Sum.inr.inj (congrArg (fun e : Site h d k×Site h d k=>e.1.1) eqn))
    obtain ⟨rfl,ports⟩:=Sigma.mk.inj_iff.mp sites
    have socket : occupiedStagePort π t (p,false)=occupiedStagePort π t (q,false):=eq_of_heq ports
    have payload : p=q:=congrArg Prod.fst ((occupiedStagePort π t).injective socket)
    have signed : l=m:=Option.some.inj (congrArg (fun e : Site h d k×Site h d k=>e.2.2) eqn)
    subst q
    subst m
    rfl

theorem catalyst_ends_injective :
    Function.Injective (fun a : Columns h d×Fin k=>(((a.1,some (a.2,false)),(a.1,some (a.2,true))) : Site h d k×Site h d k)) := by
  rintro ⟨c,i⟩ ⟨e,j⟩ eqn
  have col:=congrArg (fun x : Site h d k×Site h d k=>x.1.1) eqn
  have axis:=Option.some.inj (congrArg (fun x : Site h d k×Site h d k=>x.1.2) eqn)
  exact Prod.ext col (congrArg Prod.fst axis)

end ProbeStage.CoreBoard
end Hierarchy

end OAI

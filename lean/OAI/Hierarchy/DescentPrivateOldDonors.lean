import OAI.Hierarchy.DescentPrivateWireOrigin
import OAI.Hierarchy.DescentBundleSelected

namespace OAI
/-! # Carried live p-words at a real old site and the empty hidden space of born parties -/
namespace Hierarchy.DescentBundleHistory
open DescentKernelHistory Computability.BorderVNP.Crossing DescentSixParty
open scoped Classical
noncomputable section
variable {Tag A B U : Type} {w : A→ℕ} {w' : B→ℕ} {p : ℕ} (hp : 0<p)
variable {r : BitRecipe Tag A w} (s : Shape p r)

theorem used_iff_key (word : Private r p) :
    (s.recipe hp).Used word ↔ ∃u b,Sum.inr b∈s.keys u ∧ privateIndex hp b=word := by
  constructor
  · rintro ⟨u,j,read⟩
    change ((s.keys u)[j.val]).map id (privateIndex hp)=Sum.inr word at read
    cases hj : (s.keys u)[j.val] with
    | inl a=>simp [hj] at read
    | inr b=>
      refine ⟨u,b,?_,Sum.inr.inj (by simpa only [hj,Sum.map_inr] using read)⟩
      rw [←hj]
      exact List.getElem_mem j.isLt
  · rintro ⟨u,b,mem,eqn⟩
    obtain ⟨j,good,jread⟩:=List.mem_iff_getElem.mp mem
    refine ⟨u,⟨j,good⟩,?_⟩
    change ((s.keys u)[j]).map id (privateIndex hp)=Sum.inr word
    simp only [jread,Sum.map_inr,eqn]

variable {route : BitRef w→BitRef w'} (f : BlockMap p w w' route)
theorem reroute_keys (v : r.Node) :
    (s.reroute f).keys v=(s.keys v).map (Sum.map f.map id) := by
  simp [Shape.keys,Shape.rows,Shape.reroute,Slice.names,Slice.map,List.map_flatMap,List.map_ofFn,Function.comp_def]
  simp only [List.flatMap_def, List.map_ofFn, Slice.names, Function.comp_def]
  rfl

theorem reroute_used (word : Private r p) :
    ((s.reroute f).recipe hp).Used word ↔ (s.recipe hp).Used word := by
  refine (used_iff_key hp (s.reroute f) word).trans (Iff.trans ?_ (used_iff_key hp s word).symm)
  constructor
  · rintro ⟨u,b,mem,eqn⟩
    have mapped : Sum.inr b ∈ (s.keys u).map (Sum.map f.map id) :=
      (congrArg (fun xs => Sum.inr b ∈ xs) (reroute_keys s f u)).mp mem
    obtain ⟨x,old,read⟩:=List.mem_map.mp mapped
    cases x with
    | inl a=>simp at read
    | inr a=>
      have ab : a=b:=Sum.inr.inj read
      exact ⟨u,b,ab ▸ old,eqn⟩
  · rintro ⟨u,b,mem,eqn⟩
    refine ⟨u,b,?_,eqn⟩
    exact (congrArg (fun xs => Sum.inr b ∈ xs) (reroute_keys s f u)).mpr
      (List.mem_map.mpr ⟨.inr b,mem,rfl⟩)

variable {F P I : Type} [Field F] [Fintype I] {D Z : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F D P bits) (B0 : BitDescription W) (G : PoweredGadget F)
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (room : ∀i,z i≤Z)
variable (prof : I→Profile G.C) (old : ∀v,Shape p (B0.recipe v)) (divides : ∀e,p∣W.graph.width e)
    (pins : ∀q,p∣bits q) (units : ∀i,p∣z i)
local notation "N" => W.graph
local notation "M" => GadgetNetwork.physical N pick (branchWidth G z prof)
local notation "s0" => physicalShape W B0 G pick z room prof hp old divides pins units

/-- The occurrence at an expanded site carries its genuine old live-word label.
New matrix parties have only external legs. -/
def physicalDonor : OccupiedWord (M) (physicalBits G W.toWorld pick z room prof B0.recipe) (s0) hp ↪
    OccupiedWord N B0.recipe old hp where
  toFun
    | ⟨.inl u,h⟩ => ⟨u,h.val,(reroute_used hp (old u) (carriedMap W G pick z prof u) h.val).mp h.property⟩
    | ⟨.inr _,h⟩ => h.val.1.elim
  inj' := by
    rintro ⟨u|i,h⟩ ⟨v|j,h'⟩ eqn
    · have same : u=v := congrArg Sigma.fst eqn
      subst v
      apply congrArg (Sigma.mk (Sum.inl u))
      apply Subtype.ext
      exact congrArg (fun t : ((old u).recipe hp).UsedWord=>t.val) (eq_of_heq (Sigma.mk.inj eqn).2)
    · exact h'.val.1.elim
    · exact h.val.1.elim
    · exact h.val.1.elim

end
end Hierarchy.DescentBundleHistory

end OAI

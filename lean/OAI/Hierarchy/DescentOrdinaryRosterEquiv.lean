import OAI.Hierarchy.DescentLocalDonorAgreement
import OAI.Hierarchy.DescentLocalNodeOwners

namespace OAI
/-! # Encoded origin fibre of the ordinary vertex's scalar store -/
namespace Hierarchy.DescentOrdinaryLocalBirth
open DescentSixParty DescentKernelHistory Computability.BorderVNP.Crossing DescentNetworkPartition DescentCompiler
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P J V I T C : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    [Fintype I] [Fintype T] [Fintype C] {d k i D K Z d₁ d₂ : ℕ}
    {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule)
    (ready : A.StateBounds S i) (desc : BitDescription W) (pick : I×Fin 2↪W.graph.Edge)
    (z : I→ℕ) (room : ∀i,z i≤Z) (prof : I→Profile G.C) (picked : ∀i,pick (i,0)∈W.core)
local notation "N" => W.graph
local notation "M" => GadgetNetwork.physical N pick (branchWidth G z prof)
local notation "r₀" => physicalBits G W.toWorld pick z room prof desc.recipe
variable (a : GadgetNetwork.Site (I:=I) W.graph→T) (b : T→C)
variable (x₁ : T→EuclideanSpace ℝ (Fin d₁)) (x₂ : C→EuclideanSpace ℝ (Fin d₂))
    (ok₁ : ∀t,‖x₁ t‖≤1) (ok₂ : ∀t,‖x₂ t‖≤1)
local notation "mid" => quotient M a x₁ ok₁
local notation "r₁" => quotientBits M a x₁ ok₁ r₀
local notation "r₂" => quotientBits mid b x₂ ok₂ r₁
local notation "loc" => (b∘a)
variable (c : C)
local notation "Roster" => Σt : {t : GadgetNetwork.Site (I:=I) W.graph //loc t=c},(r₀ t.val).Node
abbrev rawSiteOf (w : NodeOrder.All desc ⊕ I×Fin 6) : (GadgetNetwork.physical W.graph pick (branchWidth G z prof)).Site :=
  match w with
  | .inl u=>.inl u.1
  | .inr t=>.inr t

def originFiber : Roster ≃ {w : NodeOrder.All desc ⊕ I×Fin 6 //loc (rawSiteOf desc pick z prof w)=c} where
  toFun
    | ⟨⟨.inl u,h⟩,x⟩=>⟨.inl ⟨u,x⟩,h⟩
    | ⟨⟨.inr t,h⟩,_⟩=>⟨.inr t,h⟩
  invFun
    | ⟨.inl ⟨u,x⟩,h⟩=>⟨⟨.inl u,h⟩,x⟩
    | ⟨.inr t,h⟩=>⟨⟨.inr t,h⟩,()⟩
  left_inv := by rintro ⟨⟨u|t,h⟩,x⟩ <;> first | rfl
  right_inv := by rintro ⟨⟨u,x⟩|t,h⟩ <;> rfl

def coefficientFiber : (r₂ c).Node ≃ {w : NodeOrder.All desc ⊕ I×Fin 6 //loc (rawSiteOf desc pick z prof w)=c} :=
  (roster desc pick z room prof a b x₁ x₂ ok₁ ok₂ c).trans (originFiber desc pick z room prof a b c)

theorem coefficientFiber_read (n : (r₂ c).Node) :
    (coefficientFiber desc pick z room prof a b x₁ x₂ ok₁ ok₂ c n).val=
      origin desc pick z room prof a b c (roster desc pick z room prof a b x₁ x₂ ok₁ ok₂ c n) := by
  unfold coefficientFiber
  change (originFiber desc pick z room prof a b c (roster desc pick z room prof a b x₁ x₂ ok₁ ok₂ c n)).val=_
  generalize roster desc pick z room prof a b x₁ x₂ ok₁ ok₂ c n = t at *
  cases t with
  | mk t node=>rcases t with ⟨u|t,h⟩ <;> rfl

/-! Two published directories enumerate the same coefficient domain once. -/
theorem equal_prefix {α β γ : Type} [Fintype α] [Fintype β] (e : α ≃ β) (a : α→γ) (b : β→γ) (value : γ→ℕ)
    (read : ∀t,b (e t)=a t) (u : α) :
    (Finset.univ.filter (fun t=>value (a t)<value (a u))).card=
      (Finset.univ.filter (fun t=>value (b t)<value (b (e u)))).card := by
  classical
  have map : {t : α // value (a t)<value (a u)} ≃ {t : β // value (b t)<value (b (e u))} :=e.subtypeEquiv (fun x=>by simp [read])
  simpa only [Fintype.card_subtype] using Fintype.card_congr map

end
end Hierarchy.DescentOrdinaryLocalBirth

end OAI

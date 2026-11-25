import OAI.Hierarchy.DescentOrdinaryNodeOrder
import OAI.Hierarchy.DescentOrdinaryDonorHalo
import OAI.Hierarchy.DescentSharedCableNames
import OAI.Hierarchy.DescentPhysicalOrder

namespace OAI
/-! # Refreshing the local atom order from bounded donor and party fields -/
namespace Hierarchy.DescentOrdinaryLocalBirth
open DescentSixParty DescentKernelHistory Computability.BorderVNP.Crossing DescentNetworkPartition
open DescentCableDonorNames DescentSharedCableNames
open scoped Classical
noncomputable section
variable {F P J V I T C : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    [Fintype I] [Fintype T] [Fintype C]
    {d k i D K Z d₁ d₂ : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
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
variable (halo : Halo C W.graph.Site D)
    (oldHere : ∀u : W.graph.Site,u∈halo.member (b (a (.inl u))))
    (newHere : ∀i j,W.graph.src (pick (i,0))∈halo.member (b (a (.inr (i,j)))))
    (oldRank : ∀u,(desc.recipe u).Node ↪ Fin K)

abbrev Width (D K cap : ℕ) := D*(K+cap*6)

def roster (c : C) : (r₂ c).Node ≃ Σt : {t : GadgetNetwork.Site (I:=I) W.graph //loc t=c},(r₀ t.val).Node where
  toFun x:=⟨⟨x.2.1.val,(congrArg b x.2.1.property).trans x.1.property⟩,x.2.2⟩
  invFun x:=⟨⟨a x.1.val,x.1.property⟩,⟨x.1.val,rfl⟩,x.2⟩
  left_inv := by rintro ⟨⟨u,h⟩,⟨t,h'⟩,n⟩;cases h';rfl
  right_inv := by rintro ⟨⟨t,h⟩,n⟩;rfl

def book (c : C) : (Σt : {t : GadgetNetwork.Site (I:=I) W.graph //loc t=c},(r₀ t.val).Node) ↪ Fin (Width D K A.cap) where
  toFun
    | ⟨⟨.inl u,h⟩,n⟩=>finProdFinEquiv (halo.slot c ⟨u,h ▸ oldHere u⟩,finSumFinEquiv (.inl (oldRank u n)))
    | ⟨⟨.inr (i,j),h⟩,_⟩=>finProdFinEquiv (halo.slot c ⟨W.graph.src (pick (i,0)),h ▸ newHere i j⟩,
        finSumFinEquiv (.inr (finProdFinEquiv (Stage.outgoing A native S ready
          ⟨pick (i,0),A.quantum_positive _ (picked i)⟩,j))))
  inj' := by
    rintro ⟨⟨u|⟨i,j⟩,h⟩,n⟩ ⟨⟨v|⟨i',j'⟩,h'⟩,m⟩ eqn
    all_goals
      obtain ⟨donor, body⟩ := Prod.mk.inj ((finProdFinEquiv (m:=D) (n:=K+A.cap*6)).injective eqn)
      have tagEq := (finSumFinEquiv (m:=K) (n:=A.cap*6)).injective body
    · have site : u=v := congrArg Subtype.val ((halo.slot c).injective donor)
      subst v
      have nodes : n=m := (oldRank u).injective (Sum.inl.inj tagEq)
      cases nodes
      rfl
    · cases tagEq
    · cases tagEq
    · have site : W.graph.src (pick (i,0))=W.graph.src (pick (i',0)) :=
        congrArg Subtype.val ((halo.slot c).injective donor)
      obtain ⟨ticket, party⟩ := Prod.mk.inj ((finProdFinEquiv (m:=A.cap) (n:=6)).injective (Sum.inr.inj tagEq))
      have prev:=Stage.outgoing_identify A native S ready
        ⟨pick (i,0),A.quantum_positive _ (picked i)⟩ ⟨pick (i',0),A.quantum_positive _ (picked i')⟩ site
        ticket
      have iEq : i=i' := congrArg Prod.fst (pick.injective (congrArg Subtype.val prev))
      subst i'
      cases party
      cases n
      cases m
      rfl

def short (c : C) : (r₂ c).Node ↪ Fin (Width D K A.cap) :=
  (roster desc pick z room prof a b x₁ x₂ ok₁ ok₂ c).toEmbedding.trans
    (book A native S ready desc pick z room prof picked a b halo oldHere newHere oldRank c)

def compact (c : C) : (r₂ c).Node ≃ Fin (Fintype.card (r₂ c).Node) :=
  DescentPhysicalOrder.physical ((short A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂
    halo oldHere newHere oldRank c).trans Fin.valEmbedding)

theorem compact_read (c : C) (u : (r₂ c).Node) :
    let rank:=short A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c
    (compact A native S ready desc pick z room prof picked a b x₁ x₂ ok₁ ok₂ halo oldHere newHere oldRank c u).val=
      (Finset.univ.filter (fun v=>rank v<rank u)).card := DescentPhysicalOrder.physical_val _ _

end
end Hierarchy.DescentOrdinaryLocalBirth

end OAI

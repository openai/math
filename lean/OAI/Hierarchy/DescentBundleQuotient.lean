import OAI.Hierarchy.DescentBundleCombine
import OAI.Hierarchy.DescentBitQuotient

namespace OAI
/-! # Each newly contracted cable keeps the same aligned payload and digit -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentNetworkPartition DescentKernelHistory
open scoped Classical
noncomputable section
variable {P C Tag : Type} [Fintype C] {D d p : ℕ} {w : P→ℕ} (N : Network D P w)
variable (loc : N.Site→C) (pos : C→EuclideanSpace ℝ (Fin d)) (ball : ∀c,‖pos c‖≤1)
local notation "Q" => quotient N loc pos ball

def quotientBlock (c : C) (v : {u //loc u=c}) (b : BlockRef p (boundaryWidth N v.val)) :
    BlockRef p (boundaryWidth (Q) c) ⊕ BlockRef p (fun e : PrivateEdge N loc c=>N.width e.val) := by
  rcases b with ⟨e|pin,n,fits⟩
  · let incident:=e.property.imp (fun h=>(congrArg loc h).trans v.property) (fun h=>(congrArg loc h).trans v.property)
    by_cases owned : loc (N.src e.val)=loc (N.dst e.val)
    · exact .inr ⟨⟨e.val,incident.elim (fun h=>⟨h,owned.symm.trans h⟩) (fun h=>⟨owned.trans h,h⟩)⟩,n,fits⟩
    · exact .inl ⟨.inl ⟨⟨e.val,owned⟩,incident⟩,n,fits⟩
  · exact .inl ⟨.inr ⟨pin.val,(congrArg loc pin.property).trans v.property⟩,n,fits⟩

def quotientMap (c : C) (v : {u //loc u=c}) : PrivateMap p (boundaryWidth N v.val)
    (boundaryWidth (Q) c) (fun e : PrivateEdge N loc c=>N.width e.val) (quotientBit N loc pos ball c v) where
  map := quotientBlock N loc pos ball c v
  read b t := by
    rcases b with ⟨e|pin,n,fits⟩
    · by_cases owned : loc (N.src e.val)=loc (N.dst e.val) <;>
        simp [quotientBit,quotientBlock,BlockRef.atBit,owned] <;> rfl
    · rfl

def quotientShape (r : SiteBits (U:=Tag) N) (s : ∀v,Shape p (r v)) (edge : ∀e,p∣N.width e) (c : C) :
    Shape p (quotientBits N loc pos ball r c) :=
  combined _ _ _ (fun v=>s v.val) (fun e=>edge e.val) (quotientMap N loc pos ball c)

@[simp] theorem quotient_stride (r : SiteBits (U:=Tag) N) (s : ∀v,Shape p (r v))
    (edge : ∀e,p∣N.width e) (c : C) (v : {u //loc u=c}) (u j g) :
    ((quotientShape N loc pos ball r s edge c).chunk ⟨v,u⟩ j g).stride=((s v.val).chunk u j g).stride := rfl
end
end Hierarchy.DescentBundleHistory

end OAI

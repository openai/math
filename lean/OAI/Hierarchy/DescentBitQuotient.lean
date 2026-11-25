import OAI.Hierarchy.DescentLocalBitHistory
import OAI.Hierarchy.DescentBitHistoryCombine

namespace OAI
/-! # Hidden bit coordinates and surviving bit coordinates in an actual site quotient -/

namespace Hierarchy.DescentKernelHistory
open Computability.BorderVNP.Crossing DescentNetworkPartition
open scoped Classical BigOperators
noncomputable section
variable {F U P C : Type} [Field F] [Fintype C] {D d : ℕ} {w : P→ℕ} (N : Network D P w)
variable (loc : N.Site→C) (pos : C→EuclideanSpace ℝ (Fin d)) (ball : ∀c,‖pos c‖≤1)
local notation "Q" => quotient N loc pos ball

def quotientBit (c : C) (v : {u //loc u=c}) : BitRef (boundaryWidth N v.val)→
    BitRef (boundaryWidth (Q) c) ⊕ BitRef (fun e : PrivateEdge N loc c=>N.width e.val)
  | ⟨.inr p,j⟩=>.inl ⟨.inr ⟨p.val,(congrArg loc p.property).trans v.property⟩,j⟩
  | ⟨.inl e,j⟩=>
    let incident:=e.property.imp (fun h=>(congrArg loc h).trans v.property) (fun h=>(congrArg loc h).trans v.property)
    if owned : loc (N.src e.val)=loc (N.dst e.val) then
      .inr ⟨⟨e.val,incident.elim (fun h=>⟨h,owned.symm.trans h⟩) (fun h=>⟨owned.trans h,h⟩)⟩,j⟩
    else .inl ⟨.inl ⟨⟨e.val,owned⟩,incident⟩,j⟩

def quotientBits (r : SiteBits (U:=U) N) (c : C) :=
  BitRecipe.combineBits (fun v : {u //loc u=c}=>r v.val) (fun e : PrivateEdge N loc c=>N.width e.val)
    (quotientBit N loc pos ball c)

theorem quotient_reads (s : U→List (List Bool)→F) (r : SiteBits (U:=U) N) (T : N.Tables F)
    (valid : ReadsBits N s r T) : ReadsBits (Q) s (quotientBits N loc pos ball r) (tables N loc pos ball T) := by
  apply (reads_iff_local ..).mpr
  intro c read pins
  rw [quotientBits,BitRecipe.combine_bits_value]
  unfold tables
  apply Finset.sum_congr (by ext x;simp only [Finset.mem_univ])
  intro hidden _
  apply Finset.prod_congr rfl
  intro v _
  rw [←(reads_iff_local N s r T).mp valid v.val]
  apply congrArg ((r v.val).value s)
  funext z
  rcases z with ⟨e|p,j⟩
  · by_cases h : loc (N.src e.val)=loc (N.dst e.val) <;> simp [quotientBit,h,localBit,localWord]
  · rfl

/-- Every carried operand still contains exactly its original number of bits. -/
theorem quotient_atom_bits (r : SiteBits (U:=U) N) (c : C) (v : {u //loc u=c}) (i : (r v.val).Node) :
    (quotientBits N loc pos ball r c).nodeBits ⟨v,i⟩=(r v.val).nodeBits i := rfl

end
end Hierarchy.DescentKernelHistory

end OAI

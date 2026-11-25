import OAI.Hierarchy.DescentPrivateOccurrenceRoute
import OAI.Hierarchy.DescentOrdinaryNodeOrder

namespace OAI
/-! Source node, source argument and surviving public word at an arbitrary occurrence of two coalescences. -/
namespace Hierarchy.DescentBundleHistory
open Computability.BorderVNP.Crossing DescentNetworkPartition DescentKernelHistory
open scoped Classical
noncomputable section
variable {P C Tag : Type} [Fintype C] {d d₁ p : ℕ} {bits : P→ℕ}
variable (N : Network d P bits) (loc : N.Site→C) (pt : C→EuclideanSpace ℝ (Fin d₁))
    (ok : ∀t,‖pt t‖≤1)
variable (r : SiteBits (U:=Tag) N) (s : ∀v,Shape p (r v)) (ed : ∀e,p∣N.width e) (hp : 0<p)
local notation "Q" => quotient N loc pt ok
local notation "qr" => quotientBits N loc pt ok r
local notation "qs" => quotientShape N loc pt ok r s ed

variable {D : Type} [Fintype D] {d₂ : ℕ} (outer : C→D) (xy : D→EuclideanSpace ℝ (Fin d₂))
    (room : ∀t,‖xy t‖≤1)
local notation "Q₂" => quotient (Q) outer xy room
local notation "r₂" => quotientBits (Q) outer xy room (qr)
local notation "s₂" => quotientShape (Q) outer xy room (qr) (qs) (fun e => ed (Subtype.val e))
local notation "qNode" => addDonor N loc pt ok r
local notation "nodeArity" => target_arity N loc pt ok r s ed hp
local notation "nextArity" => target_arity (Q) outer xy room (qr) (qs) (fun e => ed (Subtype.val e)) hp
local notation "firstRead" => nextArg N loc pt ok r hp
local notation "lastRead" => nextArg (Q) outer xy room (qr) hp

local notation "origin" => Equiv.trans (DescentKernelHistory.NodeOrder.quotientNames (Q) outer xy room (qr))
  (DescentKernelHistory.NodeOrder.quotientNames N loc pt ok r)
local notation "resultType" => (Σc,BlockRef p (boundaryWidth (Q₂) c)⊕Private (r₂ c) p)

/-- The source is selected by the literal site and node projections in the
two measured contractions. Its argument number is unchanged. -/
theorem source_operand (node : DescentKernelHistory.NodeOrder.Global (N:=Q₂) (r₂))
    (j : Fin (((s₂ node.1).recipe hp).arity node.2)) :
    let src:=(origin) node
    ∃k : Fin (((s src.1).recipe hp).arity src.2), k.val=j.val ∧
      (⟨node.1,((s₂ node.1).recipe hp).operand node.2 j⟩ : resultType)=
        ⟨outer (loc src.1),lastRead (loc src.1) (firstRead src.1 (((s src.1).recipe hp).operand src.2 k))⟩ := by
  rcases (origin).symm.surjective node with ⟨⟨u,n⟩,rfl⟩
  let k:=(j.cast (nextArity (loc u) (qNode u n))).cast (nodeArity u n)
  refine ⟨k,rfl,?_⟩
  exact congrArg (fun arg => (⟨outer (loc u),arg⟩ : resultType))
    (double_arg N loc pt ok r s ed hp outer xy room u n k)

/-- Exterior attachment and p-block numbers remain the original ones across
both quotients; only the proofs that their homes match change. -/
theorem pin_word (v : N.Site) (a : Attached N v) (n : ℕ) (fits:(n+1)*p≤bits a.val) :
    let world : Attached (Q₂) (outer (loc v)) :=
      ⟨a.val,congrArg (outer∘loc) a.property⟩
    lastRead (loc v) (firstRead v (.inl ⟨.inr a,n,fits⟩))=.inl ⟨.inr world,n,fits⟩ := by rfl

theorem free_word (v : N.Site) (e : Incident N v) (n : ℕ) (fits:(n+1)*p≤N.width e.val)
    (kept : outer (loc (N.src e.val))≠outer (loc (N.dst e.val))) :
    let split : loc (N.src e.val)≠loc (N.dst e.val):=fun h=>kept (congrArg outer h)
    let world : Incident (Q₂) (outer (loc v)):=
      ⟨⟨⟨e.val,split⟩,kept⟩,e.property.imp (congrArg (outer∘loc)) (congrArg (outer∘loc))⟩
    lastRead (loc v) (firstRead v (.inl ⟨.inl e,n,fits⟩))=.inl ⟨.inl world,n,fits⟩ := by
  intro split world
  simp [nextArg,wordTransfer,quotientMap,quotientBlock,split,kept,world,quotient]

end
end Hierarchy.DescentBundleHistory

end OAI

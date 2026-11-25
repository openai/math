import OAI.Hierarchy.DescentPrivateWireOrigin

namespace OAI
/-! # Authentic word references at one unchanged occurrence through both contractions -/
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

def pubWords (v : N.Site) := BlockRef p (boundaryWidth N v)
def addDonor (v : N.Site) (u : (r v).Node) : (qr (loc v)).Node := ⟨⟨v,rfl⟩,u⟩

theorem target_arity (v : N.Site) (u : (r v).Node) :
    ((qs (loc v)).recipe hp).arity (addDonor N loc pt ok r v u)=((s v).recipe hp).arity u := by
  have keys := combined_keys
    (fun i : {t //loc t=loc v}=>r i.val) (fun e : PrivateEdge N loc (loc v) => N.width e.val)
    (quotientBit N loc pt ok (loc v)) (fun i=>s i.val) (fun e=>ed e.val)
    (quotientMap N loc pt ok (loc v)) ⟨v,rfl⟩ u
  exact (congrArg List.length keys).trans (List.length_map (as := (s v).keys u) _)

def nextArg (v : N.Site) := wordTransfer hp
  (fun i : {t //loc t=loc v}=>r i.val) (fun e : PrivateEdge N loc (loc v) => N.width e.val) (quotientBit N loc pt ok (loc v))
  (quotientMap N loc pt ok (loc v)) ⟨v,rfl⟩

theorem at_arg (v : N.Site) (u : (r v).Node) (j : Fin (((s v).recipe hp).arity u)) :
    ((qs (loc v)).recipe hp).operand (addDonor N loc pt ok r v u)
      (j.cast (target_arity N loc pt ok r s ed hp v u).symm)=
      nextArg N loc pt ok r hp v (((s v).recipe hp).operand u j) :=
  wordTransfer_read hp (fun i : {t //loc t=loc v}=>r i.val) (fun e : PrivateEdge N loc (loc v) => N.width e.val) (quotientBit N loc pt ok (loc v))
    (fun i=>s i.val) (fun e=>ed e.val) (quotientMap N loc pt ok (loc v)) ⟨v,rfl⟩ u j

variable {D : Type} [Fintype D] {d₂ : ℕ} (outer : C→D) (xy : D→EuclideanSpace ℝ (Fin d₂))
    (room : ∀t,‖xy t‖≤1)
local notation "r₂" => quotientBits (Q) outer xy room (qr)
local notation "s₂" => quotientShape (Q) outer xy room (qr) (qs) (fun e => ed (Subtype.val e))
local notation "qNode" => addDonor N loc pt ok r
local notation "lastNode" => addDonor (Q) outer xy room (qr)
local notation "nodeArity" => target_arity N loc pt ok r s ed hp
local notation "nextArity" => target_arity (Q) outer xy room (qr) (qs) (fun e => ed (Subtype.val e)) hp
local notation "firstRead" => nextArg N loc pt ok r hp
local notation "lastRead" => nextArg (Q) outer xy room (qr) hp

/-- Both captures use the identical operand ordinal of the same original
atom, even when several occurrences reference the exact same p-word. -/
theorem double_arg (v : N.Site) (u : (r v).Node) (j : Fin (((s v).recipe hp).arity u)) :
    ((s₂ (outer (loc v))).recipe hp).operand (lastNode (loc v) (qNode v u))
        ((j.cast (nodeArity v u).symm).cast (nextArity (loc v) (qNode v u)).symm)=
      lastRead (loc v) (firstRead v (((s v).recipe hp).operand u j)) := by
  exact (at_arg (Q) outer xy room (qr) (qs) (fun e => ed e.val) hp
    (loc v) (qNode v u) (j.cast (nodeArity v u).symm)).trans
    (congrArg (lastRead (loc v)) (at_arg N loc pt ok r s ed hp v u j))

/-- The indexed wire and its p-word number are preserved when the source
wire becomes private at the first quotient. -/
theorem first_capture (v : N.Site) (e : Incident N v) (j : ℕ)
    (fits : (j+1)*p≤N.width e.val) (same : loc (N.src e.val)=loc (N.dst e.val)) :
    ∃w : Private (r₂ (outer (loc v))) p,
      lastRead (loc v) (firstRead v (.inl ⟨.inl e,j,fits⟩))=.inr w ∧
      ∀used : ((s₂ (outer (loc v))).recipe hp).Used w,
        doubleOrigin N loc pt ok r s ed hp outer xy room ⟨_,⟨w,used⟩⟩=
          .inr (.inl ⟨e.val,⟨j,(Nat.le_div_iff_mul_le hp).mpr fits⟩⟩) := by
  let here:=e.property.imp (fun h=>congrArg loc h) (fun h=>congrArg loc h)
  let owned : PrivateEdge N loc (loc v) :=
    ⟨e.val,here.elim (fun h=>⟨h,same.symm.trans h⟩) (fun h=>⟨same.trans h,h⟩)⟩
  refine ⟨⟨.inr ⟨⟨loc v,rfl⟩,.inl owned⟩,⟨j,(Nat.le_div_iff_mul_le hp).mpr fits⟩⟩,?_,fun _=>rfl⟩
  simp [nextArg,wordTransfer,quotientMap,quotientBlock,same,owned]; rfl

theorem second_capture (v : N.Site) (e : Incident N v) (j : ℕ)
    (fits : (j+1)*p≤N.width e.val) (distinct : loc (N.src e.val)≠loc (N.dst e.val))
    (same : outer (loc (N.src e.val))=outer (loc (N.dst e.val))) :
    ∃w : Private (r₂ (outer (loc v))) p,
      lastRead (loc v) (firstRead v (.inl ⟨.inl e,j,fits⟩))=.inr w ∧
      ∀used : ((s₂ (outer (loc v))).recipe hp).Used w,
        doubleOrigin N loc pt ok r s ed hp outer xy room ⟨_,⟨w,used⟩⟩=
          .inl ⟨e.val,⟨j,(Nat.le_div_iff_mul_le hp).mpr fits⟩⟩ := by
  let here:=e.property.imp (fun h=>congrArg (outer∘loc) h) (fun h=>congrArg (outer∘loc) h)
  let owned : PrivateEdge (Q) outer (outer (loc v)) :=
    ⟨⟨e.val,distinct⟩,here.elim (fun h=>⟨h,same.symm.trans h⟩) (fun h=>⟨same.trans h,h⟩)⟩
  refine ⟨⟨.inl owned,⟨j,(Nat.le_div_iff_mul_le hp).mpr fits⟩⟩,?_,fun _=>rfl⟩
  simp [nextArg,wordTransfer,quotientMap,quotientBlock,distinct,same,owned,quotient]; rfl

theorem inherited_capture (v : N.Site) (w : ((s v).recipe hp).UsedWord) :
    ∃u : Private (r₂ (outer (loc v))) p, lastRead (loc v) (firstRead v (.inr w.val))=.inr u ∧
      ∀used : ((s₂ (outer (loc v))).recipe hp).Used u,
        doubleOrigin N loc pt ok r s ed hp outer xy room ⟨_,⟨u,used⟩⟩=.inr (.inr ⟨v,w⟩) := by
  rcases w with ⟨⟨h,j⟩,used⟩
  exact ⟨⟨.inr ⟨⟨loc v,rfl⟩,.inr ⟨⟨v,rfl⟩,h⟩⟩,j⟩,rfl,fun _=>rfl⟩

end
end Hierarchy.DescentBundleHistory

end OAI

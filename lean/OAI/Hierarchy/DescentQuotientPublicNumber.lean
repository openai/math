import OAI.Hierarchy.DescentQuotientSourceOperand
import OAI.Hierarchy.DescentNamedPublicBlock

namespace OAI
/-! An actual public raw operand at an actual compact node yields the very same
retained cable and complete p-block after the two real contractions. -/
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

def sourceArg (node : DescentKernelHistory.NodeOrder.Global (N:=Q₂) (r₂))
    (j : Fin (((s₂ node.1).recipe hp).arity node.2)) :
    Fin (((s ((origin) node).1).recipe hp).arity ((origin) node).2) :=
  (source_operand N loc pt ok r s ed hp outer xy room node j).choose

theorem source_arg_read (node : DescentKernelHistory.NodeOrder.Global (N:=Q₂) (r₂)) (j : Fin (((s₂ node.1).recipe hp).arity node.2)) :
    (sourceArg N loc pt ok r s ed hp outer xy room node j).val=j.val :=
  (source_operand N loc pt ok r s ed hp outer xy room node j).choose_spec.1

local notation "number" => fun y : resultType => Sum.elim (BlockRef.cableNumber (Q₂) (Sigma.fst y)) (fun _=>none) (Sigma.snd y)

theorem source_cable (node : DescentKernelHistory.NodeOrder.Global (N:=Q₂) (r₂)) (j : Fin (((s₂ node.1).recipe hp).arity node.2))
    (e : Incident N ((origin) node).1) (chunk : ℕ) (fits : (chunk+1)*p≤N.width e.val)
    (survives : outer (loc (N.src e.val))≠outer (loc (N.dst e.val)))
    (prev : ((s ((origin) node).1).recipe hp).operand ((origin) node).2
      (sourceArg N loc pt ok r s ed hp outer xy room node j)=.inl ⟨.inl e,chunk,fits⟩) :
    ∃u : Incident (Q₂) node.1,∃budget : (chunk+1)*p≤(Q₂).width u.val,
      u.val.val.val=e.val ∧ ((s₂ node.1).recipe hp).operand node.2 j=.inl ⟨.inl u,chunk,budget⟩ := by
  have real:=(source_operand N loc pt ok r s ed hp outer xy room node j).choose_spec.2
  change (⟨node.1,((s₂ node.1).recipe hp).operand node.2 j⟩:resultType)=
    ⟨outer (loc ((origin) node).1),lastRead (loc ((origin) node).1)
      (firstRead ((origin) node).1 (((s ((origin) node).1).recipe hp).operand ((origin) node).2
        (sourceArg N loc pt ok r s ed hp outer xy room node j)))⟩ at real
  rw [prev] at real
  have kept := free_word N loc pt ok r hp outer xy room _ e chunk fits survives
  have passage := congrArg (fun result => (⟨outer (loc ((origin) node).1), result⟩ : resultType)) kept
  have read := congrArg (number) (real.trans passage)
  cases chosen:((s₂ node.1).recipe hp).operand node.2 j with
  | inr w =>
    rw [chosen] at read
    contradiction
  | inl block =>
    rw [chosen] at read
    rcases block with ⟨cable|pin,b,capacity⟩
    · change some (cable.val,b)=some (_,chunk) at read
      have val:=Option.some.inj read
      have offset:=congrArg Prod.snd val
      change b=chunk at offset
      subst b
      exact ⟨cable,capacity,congrArg (fun a : (Q₂).Edge=>a.val.val) (congrArg Prod.fst val),rfl⟩
    · contradiction

/-- A cable occurrence of the twice-contracted graph comes from a genuine
uncaptured cable in the unique original donor argument. -/
theorem source_cable_origin (node : DescentKernelHistory.NodeOrder.Global (N:=Q₂) (r₂)) (j : Fin (((s₂ node.1).recipe hp).arity node.2))
    (edge : Incident (Q₂) node.1) (low : ℕ) (fit : (low+1)*p≤(Q₂).width edge.val)
    (output : ((s₂ node.1).recipe hp).operand node.2 j=.inl ⟨.inl edge,low,fit⟩) :
    ∃e : Incident N ((origin) node).1,∃chunk : ℕ,∃fits : (chunk+1)*p≤N.width e.val,
      outer (loc (N.src e.val))≠outer (loc (N.dst e.val)) ∧
      ((s ((origin) node).1).recipe hp).operand ((origin) node).2
        (sourceArg N loc pt ok r s ed hp outer xy room node j)=.inl ⟨.inl e,chunk,fits⟩ := by
  let src:=(origin) node
  let arg:=sourceArg N loc pt ok r s ed hp outer xy room node j
  have physical:=(source_operand N loc pt ok r s ed hp outer xy room node j).choose_spec.2
  have shown:=congrArg (number) physical
  change (number) ⟨node.1,((s₂ node.1).recipe hp).operand node.2 j⟩=
    (number) ⟨outer (loc src.1),lastRead (loc src.1) (firstRead src.1 (((s src.1).recipe hp).operand src.2 arg))⟩ at shown
  rw [output] at shown
  cases source:((s src.1).recipe hp).operand src.2 arg with
  | inr word =>
    rw [source] at shown
    obtain ⟨h,n⟩:=word
    contradiction
  | inl block =>
    rw [source] at shown
    rcases block with ⟨e|a,chunk,wide⟩
    · by_cases live : outer (loc (N.src e.val))≠outer (loc (N.dst e.val))
      · exact ⟨e,chunk,wide,live,rfl⟩
      · have merged := not_ne_iff.mp live
        by_cases inner : loc (N.src e.val) = loc (N.dst e.val)
        · simp [nextArg,wordTransfer,quotientMap,quotientBlock,inner,quotient] at shown
          exact False.elim (Option.some_ne_none (edge.val,low) shown)
        · simp [nextArg,wordTransfer,quotientMap,quotientBlock,inner,merged,quotient] at shown
          exact False.elim (Option.some_ne_none (edge.val,low) shown)
    · exact False.elim (Option.some_ne_none (edge.val,low) shown)

end
end Hierarchy.DescentBundleHistory

end OAI

import OAI.Hierarchy.DescentNumberedFallbackKeys

namespace OAI
/-! # The two occurrences of an internal tree arc in the installed fallback gate -/

namespace Hierarchy.DescentBatchedBank
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentLaneGates
noncomputable section

/-- Installing an internal edge preserves both its private component and its local edge ID. -/
theorem installed_private_port {D d : ℕ} {E : Type} {width : E → ℕ} (N : Network D E width)
    (M : ∀ v, Network d (DescentNetworkSubstitution.Slot N v) (DescentNetworkSubstitution.slotWidth N v))
    (v : N.Site) (j : (M v).Site) (x : Boundary (M v) j) (e : (M v).Edge)
    (key : Sum.map Subtype.val Subtype.val x = .inl e) :
    Sum.map Subtype.val Subtype.val ((portMap N M v j).slot x) = .inl (.inr ⟨v,e⟩) := by
  cases x with
  | inl edge =>
    have h : edge.val = e := Sum.inl.inj key
    subst e
    rfl
  | inr socket => simp at key

end
end Hierarchy.DescentBatchedBank

namespace Hierarchy.DescentChosenRouter
open Computability.BorderVNP.Crossing DescentKernelHistory DescentResetGates DescentRotor DescentMixedRouter
open DescentContactTree DescentRouterSlots DescentOrderedWords DescentBatchedBank DescentBundleHistory
open DescentTreeLaneProgram
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

def treeArcLevel {h : ℕ} (d : Fin h) (incoming : Bool) : Fin (h+1) :=
  if incoming then d.succ else d.castSucc

def treeArcPin (incoming : Bool) : Fin 2 := if incoming then 0 else 1

variable {V I H A K : Type} [Fintype V] [DecidableEq V] [Fintype I] [Fintype H] [Fintype A] [Field K]
  {k n h C₀ bits u N : ℕ} (P : Placement V I H A k (2^n)) (G : NonlinearExpanders.Graph n h)
  (hw : 0<bits) (pay : ℝ) (hardware : Hardware (K:=K) (C₀:=C₀) (u:=u) P G hw pay)
  (key : I ↪ Fin N) (D m p : ℕ) (hp : 0<p) (fit : u=m*p) (s : Bool) (t : H)
local notation "selection" => selected P G hw pay hardware
local notation "bank" => DescentMixedRouter.network G hw u P.contact P.input P.site P.owner P.align selection D
local notation "programAt" => sizedProgram G hw u m p hp fit P.contact P.input P.site P.owner P.align key D selection
local notation "bk" => P.fallbackBook s t
local notation "code" => DescentFixedNamedContact.code (bk).codes (link P.contact P.owner s (.inr t))
local notation "ids" => DescentOrderedReset.itemKey key P.contact P.owner s (.inr t)
variable (e : Item P.contact P.owner s (.inr t)) (batch : Fin m) (depth : Fin (P.fallbackBook s t).height) (incoming : Bool)
local notation "level" => treeArcLevel depth incoming
local notation "node" => (⟨level,prefixAt code (level).val e⟩ : Physical.Site (bk).height)
local notation "site_" => (⟨(s,.inr t),node⟩ : (bank).Site)
local notation "gate" => installedTreeGate P G hw pay hardware key D m p hp fit s t node ⟨e,rfl⟩ batch
local notation "edge_" => (⟨depth,prefixAt code (depth.val+1) e⟩ : Physical.Edge (bk).height)

theorem treeArcArity : ((programAt site_).op gate).arity = 2 := by
  subst u
  rfl

local notation "formalPin" => (treeArcPin incoming).cast (treeArcArity P G hw pay hardware key D m p hp fit s t e batch depth incoming).symm

/-- The actual installed formal operand, at either end of the same tree edge. -/
def treeArcLane := ((programAt site_).op gate).arg formalPin

local notation "lane_" => treeArcLane P G hw pay hardware key D m p hp fit s t e batch depth incoming

/-- Both incidences retain the original private arc, as well as the item's
chronological offset in this prefix and its unit stride. -/
theorem installed_tree_arc :
    Sum.map Subtype.val Subtype.val (lane_).port = .inl (.inr ⟨(s,.inr t),edge_⟩) ∧
      (lane_).start=batchStart (Contact.cellKey ids code (depth.val+1) (prefixAt code (depth.val+1) e))
        ⟨e,rfl⟩ m p batch ∧ (lane_).stride=1 := by
  subst u
  let raw := DescentTreeLaneProgram.program D P.contact P.input P.site P.owner P.align m p hp s (.inr t)
    (bk).codes key (2^n) node
  let l := (raw.op (⟨e,rfl⟩,batch)).arg (treeArcPin incoming)
  have field : physicalFields D P.contact P.input P.site P.owner m p s (.inr t) (bk).codes l =
      (.inl edge_,batchStart (Contact.cellKey ids code (depth.val+1) (prefixAt code (depth.val+1) e))
        ⟨e,rfl⟩ m p batch,1) := by
    cases incoming with
    | false =>
      have step := following_fields D P.contact P.input P.site P.owner P.align m p hp s (.inr t)
        (bk).codes key (2^n) e batch depth.castSucc
      simp only [Fin.lastCases_castSucc] at step
      refine step.trans ?_
      congr 2
      apply congrArg (fun inst => @batchStart _ inst _ _ _ m p batch)
      exact Subsingleton.elim _ _
    | true =>
      have step := previous_fields D P.contact P.input P.site P.owner P.align m p hp s (.inr t)
        (bk).codes key (2^n) e batch depth.succ
      simp only [Fin.cases_succ] at step
      refine step.trans ?_
      congr 2
      apply congrArg (fun inst => @batchStart _ inst _ _ _ m p batch)
      exact Subsingleton.elim _ _
  let rack := DescentRouterBank.network D P.contact P.input P.site P.owner (fun _ : I => m*p)
  let devices := fun a : rack.Site => device G hw (m*p) P.contact P.input P.site P.owner P.align
    (D:=D) (selected P G hw pay hardware a.1 a.2)
  exact ⟨installed_private_port rack devices (s,.inr t) node l.port edge_ (congrArg Prod.fst field),
    congrArg (fun x => x.2.1) field,congrArg (fun x => x.2.2) field⟩

local notation "unpacked" => DescentFixedExceptionalRouter.device D P.contact P.input P.site P.owner
  (fun _ : I => m*p) s (.inr t) (bk).codes
local notation "rawOp" => DescentTreeLaneProgram.program D P.contact P.input P.site P.owner P.align m p hp
  s (.inr t) (bk).codes key (2^n) node
local notation "sourceLane" => ((rawOp).op (⟨e,rfl⟩,batch)).arg (treeArcPin incoming)

/-- Offset and population transported from the two lanes used by the literal
fallback decoder to the physical equality gate. -/
theorem tree_arc_measure :
    (lane_).count (fun x => boundaryWidth bank site_ x/p) =
      (sourceLane).count (fun x => boundaryWidth unpacked node x/p) ∧
      (lane_).bundleStart=(sourceLane).bundleStart := by
  subst u
  let rack := DescentRouterBank.network D P.contact P.input P.site P.owner (fun _ : I => m*p)
  let devices := fun a : rack.Site => device G hw (m*p) P.contact P.input P.site P.owner P.align
    (D:=D) (selected P G hw pay hardware a.1 a.2)
  exact ⟨(portMap rack devices (s,.inr t) node).lane_count sourceLane,rfl⟩

/-- The same block reference returned by the original two-operand gate
key theorem, including its bank-side incident proof. -/
theorem tree_arc_wordBlock
    (target : ∀ x, boundaryWidth bank site_ x = boundaryWidth bank site_ x/p*p)
    (source : ∀ x, boundaryWidth unpacked node x = boundaryWidth unpacked node x/p*p)
    (j : Fin ((sourceLane).count (fun x => boundaryWidth unpacked node x/p))) :
    laneBlock (fun x => boundaryWidth bank site_ x/p) target hp lane_
        (j.cast (tree_arc_measure P G hw pay hardware key D m p hp fit s t e batch depth incoming).1.symm) =
      (installedTreePorts P G hw pay hardware D m p fit s t node).wordBlock
        (laneBlock (fun x => boundaryWidth unpacked node x/p) source hp sourceLane j) := by
  subst u
  rfl

end
end Hierarchy.DescentChosenRouter

end OAI

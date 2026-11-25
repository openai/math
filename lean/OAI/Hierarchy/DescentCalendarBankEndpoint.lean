import OAI.Hierarchy.DescentFallbackRootSocket
import OAI.Hierarchy.DescentInstalledTreeArc

namespace OAI
/-! # Final hosts of the genuine installed bank edge endpoints -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentResetLocalRoster DescentParallelBase DescentResetAttachments DescentCompiler DescentColonies
open DescentSharedCableNames
open DescentChosenRouter DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks DescentContactTree
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "A₁" => B.next.placement
local notation "siteNames" => installedNames old (T).home (placement).input (T).hub same (Z).bank (Z).tables

/-- Both physical endpoints are still the original source and destination after
installing the selected bank in the old world. -/
theorem bank_edge_nodes (a : (Z).bank.Edge) :
    siteNames ((coarse).graph.src ((motherNames B).symm (.inr (.inr a))))=.inr ((Z).bank.src a) ∧
    siteNames ((coarse).graph.dst ((motherNames B).symm (.inr (.inr a))))=.inr ((Z).bank.dst a) := by
  let e := (motherNames B).symm (.inr (.inr a))
  have read := sourceFields_read old (T).home (placement).input (T).hub same (Z).bank (Z).tables e
  change physicalFields _ _ _ _ _ _ _ e=sourceFields _ _ _ _ _ ((wires) ((wires).symm (.inr (.inr a)))) at read
  rw [Equiv.apply_symm_apply] at read
  exact ⟨congrArg RawFields.src read,congrArg RawFields.dst read⟩

/-- Following either end of a real bank edge reaches the original receiver
under precisely the same site renaming as the reset history. -/
theorem bank_end_follows (a : (Z).bank.Edge) (face : Bool) (v : (Z).bank.Site)
    (endpoint : (if face then (Z).bank.dst a else (Z).bank.src a)=v) :
    let e := (motherNames B).symm (.inr (.inr a))
    (if face then (blocks B).dst e else (blocks B).src e)=treeReceiver B v := by
  intro e
  cases face with
  | false =>
    change Stage.home A₁ (hop _)=Stage.home A₁ (hop _)
    apply congrArg (fun x : (coarse).graph.Site => Stage.home A₁ (hop x))
    apply (siteNames).injective
    rw [Equiv.apply_symm_apply,(bank_edge_nodes B a).1]
    exact congrArg Sum.inr endpoint
  | true =>
    change Stage.home A₁ (hop _)=Stage.home A₁ (hop _)
    apply congrArg (fun x : (coarse).graph.Site => Stage.home A₁ (hop x))
    apply (siteNames).injective
    rw [Equiv.apply_symm_apply,(bank_edge_nodes B a).2]
    exact congrArg Sum.inr endpoint

variable (s : Bool) (t : B.reset.Fallback)
local notation "book_" => (placement).fallbackBook s t
local notation "contact_" => DescentRouterSlots.link (placement).contact (placement).owner s (.inr t)
local notation "name_" => DescentFixedNamedContact.code (book_).codes contact_
variable (e : DescentRouterSlots.Item B.reset.placement.contact B.reset.placement.owner s (.inr t))
  (level : Fin (B.reset.placement.fallbackBook s t).height) (incoming : Bool)
local notation "leaf_" => (book_).codes (contact_ e)
local notation "path_" => DescentTreePrefixIntervals.cut (Nat.succ_le_of_lt level.isLt) leaf_
local notation "site_" => (⟨(s,.inr t),⟨treeArcLevel level incoming,prefixAt name_ (treeArcLevel level incoming).val e⟩⟩ : (Z).bank.Site)
local notation "wire_" => privateWire B (fallOccurrence B s t ⟨level,path_⟩)

/-- An incoming operand uses the successor prefix. An outgoing operand uses
the preceding prefix. Both belong to the physical site of this very gate. -/
theorem tree_arc_receiver :
    (if incoming then (blocks B).dst wire_ else (blocks B).src wire_)=treeReceiver B site_ := by
  let edge : (Z).bank.Edge := .inr ⟨(s,.inr t),⟨level,path_⟩⟩
  apply bank_end_follows B edge incoming site_
  cases incoming with
  | true =>
    change (⟨(s,.inr t),⟨level.succ,path_⟩⟩ : (Z).bank.Site)=
      ⟨(s,.inr t),⟨level.succ,prefixAt name_ (level.val+1) e⟩⟩
    apply congrArg (fun pth : Node (level.val+1) =>
      (⟨(s,.inr t),⟨level.succ,pth⟩⟩ : (Z).bank.Site))
    funext j
    have below := j.isLt.trans_le (Nat.succ_le_of_lt level.isLt)
    simp [DescentTreePrefixIntervals.cut,prefixAt,DescentFixedNamedContact.code,below]
    rfl
  | false =>
    change (⟨(s,.inr t),⟨level.castSucc,fun j => path_ j.castSucc⟩⟩ : (Z).bank.Site)=
      ⟨(s,.inr t),⟨level.castSucc,prefixAt name_ level.val e⟩⟩
    apply congrArg (fun pth : Node level.val =>
      (⟨(s,.inr t),⟨level.castSucc,pth⟩⟩ : (Z).bank.Site))
    funext j
    have below := j.isLt.trans level.isLt
    simp [DescentTreePrefixIntervals.cut,prefixAt,DescentFixedNamedContact.code,below]
    rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

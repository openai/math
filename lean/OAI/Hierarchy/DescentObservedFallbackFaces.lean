import OAI.Hierarchy.DescentFallbackFlatAddress
import OAI.Hierarchy.DescentResetParentOriginHosts

namespace OAI
/-! # The actual signed incidences occupied by an original fallback grain -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open DescentFallbackOperandQuery DescentNextSignedWindow DescentResetWireTags DescentTreePrefixIntervals
open DescentRouterSlots DescentContactTree
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
local notation "Host" => DescentSharedCableNames.Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "same" => funext (fun e=>((Z).allWidths e).symm)
local notation "wires" => installedWireNames (old) (T).home (placement).input (T).hub same (Z).bank (Z).tables
local notation "key" => DescentOrderedReset.grains W B.count B.order


local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)



local notation "A₁" => B.next.placement
local notation "ord₁" => B.next.order.trans Fin.valEmbedding
local notation "rr" => (Z).k-c
local notation "Y" => (2^(Z).n : ℕ)
local notation:max "Face" u:arg => Roster.Face A₁ ord₁ (blocks B) u



variable {field query lanes batches split nodes args : ℕ}
local notation "cfg" => flatConfig B field query lanes batches split nodes args
local notation:max "bk" s:arg t:arg => (placement).fallbackBook s t
local notation:max "oldItem" s:arg t:arg => DescentRouterSlots.Item (placement).contact (placement).owner s (.inr t)
local notation:max "edgeAt" s:arg t:arg e:arg => DescentRouterSlots.link (placement).contact (placement).owner s (.inr t) e
local notation:max "leafAt" s:arg t:arg e:arg => (bk s t).codes (edgeAt s t e)
local notation:max "edgePath" k:arg p:arg => DescentTreePrefixIntervals.cut (Nat.succ_le_of_lt (k).isLt) p
local notation:max "nodeWire" s:arg t:arg k:arg e:arg => privateWire B (fallOccurrence B s t ⟨k,edgePath k (leafAt s t e)⟩)
local notation:max "atEnd" edge:arg side:arg => (if side then (blocks B).dst edge else (blocks B).src edge)

private theorem unit_pos : 0<(Z).unit:=by
  rw [B.unit,←B.next.grain]
  exact Nat.mul_pos B.next.placement.unitPos G.base_pos

private theorem constant_sum_div {X : Type*} (source target : Fintype X) {u : ℕ} (hu : 0<u) :
    ((@Finset.univ X source).sum (fun _ => u))/u = @Fintype.card X target := by
  cases Subsingleton.elim source target
  let _ : Fintype X := source
  rw [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.mul_div_cancel _ hu]
  exact congrArg (@Fintype.card X) (Subsingleton.elim _ _)

/-- The private wire at a reached prefix contains exactly the original grains in that prefix. -/
theorem observed_tree_units (s : Bool) (t : (Z).Fallback) (e : oldItem s t) (n₀ : Fin (bk s t).height) :
    let keyFn := DescentFixedNamedContact.code (bk s t).codes
      (DescentRouterSlots.link (placement).contact (placement).owner s (.inr t))
    (blocks B).count (nodeWire s t n₀ e)=
      Fintype.card (DescentContactTree.Cell keyFn (n₀.val+1) (edgePath n₀ (leafAt s t e))) := by
  intro keyFn
  let segment := edgePath n₀ (leafAt s t e)
  let occurrence := fallOccurrence B s t ⟨n₀,segment⟩
  have width:=(congrArg (fun a : ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×Bool=>a.2.2.2.2.2.1)
    ((Z).privateArchive T vertexCode birth s (.inr t) ⟨n₀,segment⟩))
  change (coarse).graph.width (privateWire B occurrence) = (dev (sel s (.inr t))).width ⟨n₀,segment⟩ at width
  dsimp only [DescentChosenRouter.selected,DescentMixedRouter.device,DescentFixedExceptionalRouter.device,DescentLocalAdapters.graph,
    DescentFixedNamedContact.network,DescentFixedNamedContact.paddedTree,
    DescentContactTree.Physical.graph,DescentContactTree.Physical.nodeWidth,DescentRouterSlots.amount] at width
  change weight B (privateWire B occurrence) = _
  rw [weight_quotient,width]
  exact constant_sum_div _ _ (unit_pos B)

theorem observed_tree_count (s : Bool) (t : (Z).Fallback) (e : oldItem s t) (n₀ : Fin (bk s t).height) :
    0<(blocks B).count (nodeWire s t n₀ e) :=by
  let k₀:=n₀.val+1
  let segment:=edgePath n₀ (leafAt s t e)
  let code:=DescentFixedNamedContact.code (bk s t).codes
    (DescentRouterSlots.link (placement).contact (placement).owner s (.inr t))
  have oldIn : prefixAt code k₀ e=segment:=by
    funext j
    have hj : j.val<(bk s t).height:=lt_of_lt_of_le j.isLt (Nat.succ_le_of_lt n₀.isLt)
    simp [code,prefixAt,DescentFixedNamedContact.code,segment,DescentTreePrefixIntervals.cut,hj]
    rfl
  let witness : Cell code k₀ segment:=⟨e,oldIn⟩
  rw [observed_tree_units]
  exact Fintype.card_pos_iff.mpr ⟨witness⟩

/-- Both ends of the private edge are real signed incidences of the next clock. -/
def observedTreeFace (s : Bool) (t : (Z).Fallback) (e : oldItem s t)
    (k₀ : Fin (bk s t).height) (side : Bool) :
    Face (atEnd (nodeWire s t k₀ e) side):=
  ⟨(nodeWire s t k₀ e,side),observed_tree_count B s t e k₀,rfl⟩

theorem observed_tree_address (s : Bool) (t : (Z).Fallback) (e : oldItem s t)
    (k₀ : Fin (bk s t).height) (side : Bool) :
    let atSite:=atEnd (nodeWire s t k₀ e) side
    (cfg).treeAt s side (A).cap (bk s t).height k₀.val (start height (leafAt s t e))
      ((Z).fallLabel T t,((T).code t).2.2)=
      (Roster.addr A₁ ord₁ (blocks B) atSite (localRoster B atSite) (observedTreeFace B s t e k₀ side)).val+1 :=
  flat_tree_position B s t k₀ (leafAt s t e) (observedTreeFace B s t e k₀ side) rfl

theorem observed_contact_count (j : (placement).Contact) (e : (old).graph.Edge) (hit : (placement).contact e=j) :
    0<(blocks B).count (contactParent B j) :=by
  have width:=congrArg (fun a : ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×Bool=>a.2.2.2.2.2.1)
    ((Z).contactArchive T vertexCode birth j)
  let owners:={v : (old).graph.Edge // (placement).contact v=j}
  change (coarse).graph.width (contactParent B j)=Fintype.card owners*(Z).unit at width
  change 0<weight B (contactParent B j)
  rw [weight_quotient,width,Nat.mul_div_cancel _ (unit_pos B)]
  exact Fintype.card_pos_iff.mpr ⟨⟨e,hit⟩⟩

def observedContactFace (s : Bool) (j : (placement).Contact) (e : (old).graph.Edge) (hit : (placement).contact e=j) :
    Face (atEnd (contactParent B j) s):=
  ⟨(contactParent B j,s),observed_contact_count B j e hit,rfl⟩

theorem observed_contact_address (s : Bool) (j) (e : (old).graph.Edge) (hit : (placement).contact e=.inr j) :
    let t:=fallEnd placement s j
    let atSite:=atEnd (contactParent B (.inr j)) s
    (cfg).contactAt s (A).cap (bk s t).height (start height ((bk s t).codes (fallLeg placement s j)))
      ((Z).fallLabel T t,((T).code t).2.2)=
      (Roster.addr A₁ ord₁ (blocks B) atSite (localRoster B atSite) (observedContactFace B s (.inr j) e hit)).val+1 :=
  flat_contact_position B s j (observedContactFace B s (.inr j) e hit) rfl rfl

/-- An item of a fallback tree has exactly a fallback contact, with its true
leaf endpoint given by the same incident ticket. -/
theorem observed_fall_contact (s : Bool) (t : (Z).Fallback) (e : oldItem s t) :
    ∃j,(placement).contact e.val=.inr j ∧ fallEnd placement s j=t :=by
  have owner:=e.property
  cases eqn : (placement).contact e.val with
  | inl u=>
    rw [eqn] at owner
    cases owner
  | inr j=>
    refine ⟨j,rfl,?_⟩
    rw [eqn] at owner
    exact Sum.inr.inj owner

/-- The leaf port queried with the original tree label and padded leaf address
is the allocated next-state slot at its physical cable endpoint. -/
theorem observed_leaf_address (s : Bool) (t : (Z).Fallback) (e : oldItem s t) :
    let contactWire:=contactParent B ((placement).contact e.val)
    let atSite:=atEnd contactWire s
    (cfg).contactAt s (A).cap (bk s t).height (start height (leafAt s t e))
      ((Z).fallLabel T t,((T).code t).2.2)=
      (Roster.addr A₁ ord₁ (blocks B) atSite (localRoster B atSite)
        (observedContactFace B s ((placement).contact e.val) e.val rfl)).val+1 :=by
  obtain ⟨j,hit,rfl⟩:=observed_fall_contact B s t e
  have sameLeg : edgeAt s (fallEnd placement s j) e=fallLeg placement s j:=Subtype.ext hit
  have numbered := observed_contact_address (field:=field) (query:=query) (lanes:=lanes)
    (batches:=batches) (split:=split) (nodes:=nodes) (args:=args) B s j e.val hit
  rw [sameLeg]
  let socketAddress (contact : (placement).Contact) (seen : (placement).contact e.val=contact) :=
    let host := atEnd (contactParent B contact) s
    (Roster.addr A₁ ord₁ (blocks B) host (localRoster B host)
      (observedContactFace B s contact e.val seen)).val+1
  have transport (contact : (placement).Contact) (seen : (placement).contact e.val=contact) :
      socketAddress ((placement).contact e.val) rfl=socketAddress contact seen := by
    cases seen
    rfl
  change _=socketAddress ((placement).contact e.val) rfl
  rw [transport _ hit]
  exact numbered

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

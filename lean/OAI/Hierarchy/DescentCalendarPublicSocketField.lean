import OAI.Hierarchy.DescentCalendarProducedOperand
import OAI.Hierarchy.DescentObservedRotorFaces
import OAI.Hierarchy.DescentContactCandidateShelf

namespace OAI
/-! The marked contact and single-unit old stem issued by a public aperture resolve
to their own reached faces. On a one-unit stem the marked split has zero quotient. -/
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



variable {field query lanes batches split nodes args grain : ℕ}
local notation "cfg" => flatConfig B field query lanes batches split nodes args
open DescentPackedRotorMatrix DescentResetPublicOperandBook DescentRotorOperandQueryROM.Shape
local notation:max "cell" s:arg g:arg => DescentChosenRouter.Cells (placement) s g
local notation:max "atEnd" e:arg s:arg => (if s then (blocks B).dst e else (blocks B).src e)
local notation "landing" => localAddress («c»:=c) A before S input.valid digitsIn B.frame.basis

local notation "pubCfg" => publicOperandConfig B field query lanes batches split nodes args grain


open DescentOperandStateBanks DescentResetOperandComponents DescentOperandCandidateLookup
open DescentDatedAddressBook.ResetOutput

structure PublicSocket (host : Host) (units word : ℕ) (tag : Bool) (number : ℕ) where
  face : Face host
  address : number=(Roster.addr A₁ ord₁ (blocks B) host (localRoster B host) face).val+1
  inside : word/units<(blocks B).count face.val.1
  mark : decide (face.val.1∈(coarse).core)=tag ∨ word<units

theorem PublicSocket.observed {host : Host} {word : ℕ} {tag : Bool} {number : ℕ}
    (socket : PublicSocket B host split word tag number) (names : Host↪ℕ)
    (arg : Fin (pubCfg).args) (node : Fin (pubCfg).nodes) (x : (pubCfg).Data (Z).n)
    {H₀ G₀ candidates coeff signed : ℕ} (size : ℕ) (f₀ : DescentOperandStateBanks.Field)
    (width : max ((A₁).degree+1) ((A₁).cap+1)≤2^signed)
    (card : candidates=totalLocal B) (room : 2*candidates<2^query)
    (location : Fin H₀→Fin G₀→Option Host) (q₀ : Fin H₀→Fin G₀→Option (Fin (2*candidates)))
    (rh : Fin H₀) (rg : Fin G₀) (siteAt : location rh rg=some host)
    (issued : code room (q₀ rh rg)=(pubCfg).column (Z).graph query none (finProdFinEquiv (arg,node)) x)
    (observedKey : (pubCfg).column (Z).graph query none (finProdFinEquiv (arg,node)) x=(number:ℕ))
    (observedWord : (pubCfg).column (Z).graph coeff (some f₀) (finProdFinEquiv (arg,node)) x=
      ((produced tag split word ⟨0,1,size⟩ f₀ : ℕ):Cell coeff)) :
    let u:=referencedUnit B host socket.face split word socket.inside
    let child:=DescentSharedCableNames.Stage.live A₁ ord₁ S B.next.valid names host (GrainPorts.port A₁ ord₁ (blocks B) host u)
    let value:=(Pointer.cable child.neighbor.val (child.wire.val-child.within.val)
        (if tag then word%split else word)).fields ⟨0,1,size⟩ f₀
    value<2^coeff →
    ((pubCfg).column (Z).graph coeff (some f₀) (finProdFinEquiv (arg,node)) x).val+
      (selected q₀ (fun j h g=>nativeCandidateField signed coeff f₀ ((location h g).bind (fun site=>
        candidateRows B names site (j.cast (congrArg (2*·) card))))) rh rg).val=value := by
  intro u child value bound
  have markEq : (grainRecord B names host u).marked=decide (socket.face.val.1∈(coarse).core) := by
    exact congrArg (@decide (socket.face.val.1∈(coarse).core)) (Subsingleton.elim _ _)
  have bits : (grainRecord B names host u).marked=tag ∨ word<split := socket.mark.imp (markEq.trans ·) id
  have both : produced (grainRecord B names host u).marked split word ⟨0,1,size⟩ f₀=
      produced tag split word ⟨0,1,size⟩ f₀ ∧
      (if (grainRecord B names host u).marked then word%split else word)=(if tag then word%split else word) := by
    rcases bits with aligned|small
    · simp only [aligned,and_self]
    · cases tag <;> cases marker:(grainRecord B names host u).marked <;>
        simp [produced,Nat.div_eq_of_lt small,Nat.mod_eq_of_lt small]
  have keyAt:=observedKey.trans (congrArg (fun n : ℕ=>(n:Cell query)) socket.address)
  have fieldAt:=observedWord.trans (congrArg (fun n : ℕ=>(n:Cell coeff)) both.1.symm)
  have read:=observed_public_field B names (Z).graph (pubCfg) arg node x host socket.face word size signed coeff
    socket.inside f₀ width card room location q₀ rh rg siteAt issued keyAt fieldAt
  have fieldEq := congrArg (fun v : ℕ =>
    (Pointer.cable child.neighbor.val (child.wire.val-child.within.val) v).fields ⟨0,1,size⟩ f₀) both.2
  exact (read (lt_of_eq_of_lt fieldEq bound)).trans fieldEq

def reached_stem_socket (side : Bool) (x : (pubCfg).Data (Z).n) (e : Grain A)
    (word : ℕ) (small : word<split) :
    let host:=(blocks B).dst (stemParent B (side,oldOfGrain B e))
    let ref:=(pubCfg).oldConfig.stemAt side (A).cap ((pubCfg).oldItem x side (oldRotorCell B side e))
    PublicSocket B host split word false ref := by
  refine ⟨socketFace B side e,issued_stem_face B side x e,?_,Or.inr small⟩
  rw [Nat.div_eq_of_lt small]
  exact (socketFace B side e).property.1

def reached_contact_socket (side : Bool) (root : (Z).placement.Good) (e : cell side root) (word : ℕ)
    (owns : word/split<Fintype.card {j : (old).graph.Edge // (placement).contact j=(placement).contact e.val}) :
    let wire:=contactParent B ((placement).contact e.val)
    let host:=atEnd wire side
    let ref:=(pubCfg).rotorContactAt side (A).cap ((Z).goodLabel T root) (DescentChosenRouter.target placement side root e)
    PublicSocket B host split word true ref := by
  let hit:=original_word_contact (field:=field) (query:=query) (lanes:=lanes) (batches:=batches)
    (split:=split) (nodes:=nodes) (args:=args) (grain:=grain) B side root e
  let face:=Classical.choose hit
  have actual:=Classical.choose_spec hit
  have edge:=congrArg (fun z : (coarse).graph.Edge×Bool=>z.1) actual.1
  have pos : 0<(Z).unit := by rw [B.unit,←B.next.grain];exact Nat.mul_pos B.next.placement.unitPos G.base_pos
  have size := (contact_units B ((placement).contact e.val) pos).1
  have charged := (contact_units B ((placement).contact e.val) pos).2
  refine ⟨face,actual.2,?_,Or.inl ?_⟩
  · rw [edge,size]
    exact owns
  · rw [edge]
    exact decide_eq_true charged

local notation:max "bk" s:arg t:arg => (placement).fallbackBook s t
local notation:max "oldItem" s:arg t:arg => DescentRouterSlots.Item (placement).contact (placement).owner s (.inr t)
local notation:max "edgeAt" s:arg t:arg e:arg => DescentRouterSlots.link (placement).contact (placement).owner s (.inr t) e
local notation:max "leafAt" s:arg t:arg e:arg => (bk s t).codes (edgeAt s t e)
local notation:max "edgePath" k:arg p:arg => DescentTreePrefixIntervals.cut (Nat.succ_le_of_lt (k).isLt) p
local notation:max "nodeWire" s:arg t:arg k:arg e:arg => privateWire B (fallOccurrence B s t ⟨k,edgePath k (leafAt s t e)⟩)


private theorem public_unit_pos : 0<(Z).unit := by
  rw [B.unit,←B.next.grain]
  exact Nat.mul_pos B.next.placement.unitPos G.base_pos

/-- Every exceptional tree lane at this prefix consumes one successor grain for
each genuine old item in the prefix, including the two signs independently. -/
theorem reached_tree_units (s : Bool) (t : (Z).Fallback) (e : oldItem s t) (d₀ : Fin (bk s t).height) :
    let keyFn:=DescentFixedNamedContact.code (bk s t).codes
      (DescentRouterSlots.link (placement).contact (placement).owner s (.inr t))
    (blocks B).count (nodeWire s t d₀ e)=
      Fintype.card (DescentContactTree.Cell keyFn (d₀.val+1) (edgePath d₀ (leafAt s t e))) :=
  observed_tree_units B s t e d₀

def reached_tree_socket (side : Bool) (t : (Z).Fallback) (e : oldItem side t)
    (d₀ : Fin (bk side t).height) (faceSide : Bool) (word : ℕ)
    (owns : word/split<Fintype.card (DescentContactTree.Cell
      (DescentFixedNamedContact.code (bk side t).codes
        (DescentRouterSlots.link (placement).contact (placement).owner side (.inr t)))
      (d₀.val+1) (edgePath d₀ (leafAt side t e)))) :
    let host:=atEnd (nodeWire side t d₀ e) faceSide
    let number:=(cfg).treeAt side faceSide (A).cap (bk side t).height d₀.val (start height (leafAt side t e))
      ((Z).fallLabel T t,((T).code t).2.2)
    PublicSocket B host split word true number := by
  let face:=observedTreeFace B side t e d₀ faceSide
  refine ⟨face,observed_tree_address B side t e d₀ faceSide,?_,Or.inl ?_⟩
  · change word/split<(blocks B).count (nodeWire side t d₀ e)
    rw [reached_tree_units]
    exact owns
  · have marked:=congrFun ((Z).record_actual T vertexCode side (.inr t) ⟨d₀,edgePath d₀ (leafAt side t e)⟩) (6 : Fin 7)
    change (if nodeWire side t d₀ e∈(coarse).core then 1 else 0)=1 at marked
    change decide (nodeWire side t d₀ e∈(coarse).core)=true
    apply decide_eq_true
    by_contra away
    simp [away] at marked

def reached_leaf_socket (side : Bool) (t : (Z).Fallback) (e : oldItem side t) (word : ℕ)
    (owns : word/split<Fintype.card {j : (old).graph.Edge // (placement).contact j=(placement).contact e.val}) :
    let host:=atEnd (contactParent B ((placement).contact e.val)) side
    let number:=(cfg).contactAt side (A).cap (bk side t).height (start height (leafAt side t e))
      ((Z).fallLabel T t,((T).code t).2.2)
    PublicSocket B host split word true number := by
  have size := (contact_units B ((placement).contact e.val) (public_unit_pos B)).1
  have charged := (contact_units B ((placement).contact e.val) (public_unit_pos B)).2
  refine ⟨observedContactFace B side ((placement).contact e.val) e.val rfl,observed_leaf_address B side t e,?_,Or.inl ?_⟩
  · change word/split<(blocks B).count (contactParent B ((placement).contact e.val))
    rw [size]
    exact owns
  · exact decide_eq_true charged

/-- A reached private rotor cable has precisely the archived circuit layer
count times that edge's weighted number of physical payloads. -/
theorem private_rotor_count (side : Bool) (root : (Z).placement.Good)
    (e : (DescentCommonPalette.rotor (Z).graph).Edge) :
    (blocks B).count (privateWire B (goodOccurrence B side root e))=
      ((Z).circuit side root).layers*DescentRotorPrivateFields.price (Z).graph C (Z).width e := by
  let E := DescentCommonPalette.rotorEdgeEquiv (Z).graph d
    (DescentChosenRouter.selectedRotorLayers placement (Z).graph (Z).positive (Z).pay (Z).circuit side root)
    C (Z).width (Z).unit
  have original:=congrArg (fun v : ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×Bool=>v.2.2.2.2.2.1)
    ((Z).privateArchive T vertexCode birth side (.inl root) (E e))
  change (coarse).graph.width (privateWire B (goodOccurrence B side root e))=(dev (sel side (.inl root))).width (E e) at original
  have physical:=(Z).rotor_measured side root (E e)
  change (dev (sel side (.inl root))).width (E e)=(Z).unit*(((Z).circuit side root).layers*
    DescentRotorPrivateFields.price (Z).graph C (Z).width (E.symm (E e))) at physical
  rw [E.symm_apply_apply] at physical
  change weight B (privateWire B (goodOccurrence B side root e))=_
  rw [weight_quotient,original,physical,Nat.mul_div_cancel_left _ (public_unit_pos B)]

/-- Being fetched from a lane's flattened list already bounds its physical
word and supplies the finite unit used by the oriented candidate. -/
theorem reached_rotor_owns (side : Bool) (root : (Z).placement.Good)
    (cfg₀ : DescentRotorOperandQueryROM.Shape) (l : DescentRotorOperandQueryROM.Shape.PrivateLane (Z).graph)
    (mult p₀ levels node arg within : ℕ) (site : (DescentCommonPalette.rotor (Z).graph).Site)
    (fetch : (cfg₀.flattened (Z).graph mult levels p₀ node site)[arg]?=some (l,within))
    (levelsEq : levels=((Z).circuit side root).layers) (factors : mult=C)
    (packet : cfg₀.packet=(Z).width) (splitEq : cfg₀.batches=split) (positive : 0<split) :
    (l.start/p₀+within)/split<(blocks B).count (privateWire B (goodOccurrence B side root l.edge)) := by
  have member:=List.mem_of_getElem? fetch
  change (l,within)∈(_ : List _).flatMap _ at member
  obtain ⟨q₀,_,seen⟩:=List.mem_flatMap.mp member
  obtain ⟨j,edgeEq⟩:=List.mem_ofFn.mp seen
  change (q₀,j.val)=(l,within) at edgeEq
  have numerator : q₀.start/p₀+j.val<q₀.units (Z).graph cfg₀ mult levels := by
    have short := j.isLt
    change j.val< min _ (_-_) at short
    have room:=lt_of_lt_of_le short (Nat.min_le_right ..)
    omega
  cases edgeEq
  rw [private_rotor_count,Nat.div_lt_iff_lt_mul positive]
  simpa only [DescentRotorOperandQueryROM.Shape.PrivateLane.units,levelsEq,packet,splitEq,factors,
    Nat.mul_assoc,Nat.mul_left_comm,Nat.mul_comm] using numerator

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

import OAI.Hierarchy.DescentObservedFallbackFaces
import OAI.Hierarchy.DescentPublicOperandFlatTap

namespace OAI
/-! # True signed faces of both kinds of public rotor socket -/
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

def publicOperandConfig (field query lanes batches split nodes args grain : ℕ) : DescentResetPublicOperandBook.Config :=
  {oldConfig:=flatConfig B field query lanes batches split nodes args,packetWidth:=(Z).width,gain:=f,multiplicity:=C,grain:=grain}
local notation "pubCfg" => publicOperandConfig B field query lanes batches split nodes args grain

/-- The physical signed row of the old rotor donor is encoded in the old-item
coordinates. They are independent of the donor's root, previous ordering key, or word. -/
theorem original_word_stem (side : Bool) (x : (pubCfg).Data (Z).n) (e : Grain A)
    (j : Fin (pubCfg).oldConfig.count)
    (place : ((finProdFinEquiv.symm j : Fin (pubCfg).donors×Fin (2*(A).cap)).1.val,
      (finProdFinEquiv.symm j : Fin (pubCfg).donors×Fin (2*(A).cap)).2.val)=
      ((landing side e).1.val,(landing side e).2.val)) :
    let where_:=(blocks B).dst (stemParent B (side,oldOfGrain B e))
    (pubCfg).oldConfig.stemAt side (A).cap ((pubCfg).oldItem x side j)=
      (Roster.addr A₁ ord₁ (blocks B) where_ (localRoster B where_) (socketFace B side e)).val+1 :=by
  apply observed_socket_address B side e
  · exact congrArg Prod.fst place
  · exact congrArg Prod.snd place

/-- Read the unpadded local rotor coordinates through the genuine reset dimension. -/
def oldRotorCell (side : Bool) (e : Grain A) : Fin (2^rr*(2*(A).cap)) :=
  let pos:=landing side e
  finProdFinEquiv (Fin.cast (by rw [B.keyWidth]) pos.1,pos.2)

theorem issued_stem_face (side : Bool) (x : (pubCfg).Data (Z).n) (e : Grain A) :
    let where_:=(blocks B).dst (stemParent B (side,oldOfGrain B e))
    (pubCfg).oldConfig.stemAt side (A).cap ((pubCfg).oldItem x side (oldRotorCell B side e))=
      (Roster.addr A₁ ord₁ (blocks B) where_ (localRoster B where_) (socketFace B side e)).val+1 :=by
  apply original_word_stem
  let loc := landing side e
  let pair : Fin (2^rr) × Fin (2*(A).cap) := (Fin.cast (by rw [B.keyWidth]) loc.1,loc.2)
  have round := finProdFinEquiv.symm_apply_apply pair
  exact congrArg (fun p : Fin (2^rr) × Fin (2*(A).cap) => (p.1.val,p.2.val)) round

/-- The actual reserved contact of a good item, including its selected rotor
vertex at the public end. -/
theorem rotor_ticket_face (side : Bool) (root : (Z).placement.Good) (e : cell side root) :
    let j:=(placement).ticket ⟨e.val,paid placement side root e⟩
    (placement).contact e.val=.inl j ∧ (placement).ends side j.1=root ∧
      ((placement).outputName c side j).2=DescentChosenRouter.target placement side root e :=by
  rcases e with ⟨e,h₁⟩
  have enabled:=paid placement side root ⟨e,h₁⟩
  let j:=(placement).ticket ⟨e,enabled⟩
  have isContact : (placement).contact e=.inl j := by
    simp [Placement.contact,DescentChosenRouter.contact,enabled,j]
  have rootEq : (placement).ends side j.1=root := by
    rw [isContact] at h₁
    exact Sum.inl.inj h₁
  have targetAt (base : (placement).Good) (atBase : (placement).ends side j.1=base)
      (item : cell side base) (hit : (placement).contact item.val=.inl j) :
      DescentChosenRouter.target placement side base item=((placement).outputName c side j).2 := by
    cases atBase
    have linkEq : DescentRouterSlots.link (placement).contact (placement).owner side
        (.inl ((placement).ends side j.1)) item=⟨.inl j,rfl⟩ := Subtype.ext hit
    exact congrArg (fun address => DescentChosenRouter.tail placement side ((placement).ends side j.1) address) linkEq
  exact ⟨isContact,rootEq,(targetAt root rootEq ⟨e,h₁⟩ isContact).symm⟩

theorem original_word_contact (side : Bool) (root : (Z).placement.Good) (e : cell side root) :
    let edge:=contactParent B ((placement).contact e.val)
    let receiver:=atEnd edge side
    ∃face : Face receiver,face.val=(edge,side) ∧
      (pubCfg).rotorContactAt side (A).cap ((Z).goodLabel T root) (DescentChosenRouter.target placement side root e)=
        (Roster.addr A₁ ord₁ (blocks B) receiver (localRoster B receiver) face).val+1 :=by
  let j:=(placement).ticket ⟨e.val,paid placement side root e⟩
  obtain ⟨isContact,isRoot,isVertex⟩:=rotor_ticket_face B side root e
  dsimp only
  rw [isContact]
  let face:=observedContactFace B side (.inl j) e.val isContact
  refine ⟨face,rfl,?_⟩
  calc
    _ = (pubCfg).rotorContactAt side (A).cap ((Z).goodLabel T ((placement).ends side j.1))
        ((placement).outputName c side j).2 := by
      exact congrArg₂ ((pubCfg).rotorContactAt side (A).cap)
        (congrArg ((Z).goodLabel T) isRoot.symm) isVertex.symm
    _ = _ := flat_rotor_contact_position B side j face rfl rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

import OAI.Hierarchy.DescentResetRegisteredRelayRows
import OAI.Hierarchy.DescentCalendarPublicSocketField
import OAI.Hierarchy.DescentRetainedOriginalUnit
import OAI.Hierarchy.DescentResetTrunkMeta

namespace OAI
/-! # Opposite installed faces at a relay on an incoming grain -/
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
local notation "Host" => Stage.Host (Fin groups) B.next.V k
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
local notation "Face" u => Roster.Face A₁ ord₁ (blocks B) u



variable {field query lanes batches split nodes args grain : ℕ}
local notation "cfg" => flatConfig B field query lanes batches split nodes args
open DescentPackedRotorMatrix DescentResetPublicOperandBook DescentRotorOperandQueryROM.Shape
local notation "cell" s g => DescentChosenRouter.Cells (placement) s g
local notation "atEnd" e s => (if s then (blocks B).dst e else (blocks B).src e)
local notation "landing" => localAddress A before S input.valid digitsIn B.frame.basis

local notation "pubCfg" => publicOperandConfig B field query lanes batches split nodes args grain


open DescentOperandStateBanks DescentResetOperandComponents DescentOperandCandidateLookup
open DescentDatedAddressBook.ResetOutput


local notation "End₀" => (old).graph.Edge
local notation "land" e => (T).home ((old).graph.dst e)
local notation "trunk" e => trunkParent B (land e)
local notation "site" e => (blocks B).dst (trunk e)
local notation "inputStem" e => stemParent B (true,e)
local notation "total_" => total (cfg).toShape (A).cap

def relayTrunkFace (e : End₀) : Face (site e) :=
  ⟨(trunk e,true),Nat.zero_lt_of_lt (incoming_before_end B e),rfl⟩

def relayStemFace (e : End₀) : Face (site e) :=
  ⟨(inputStem e,false),by simpa only [stem_one] using Nat.zero_lt_one,(incoming_home B (land e) e).2 rfl⟩

theorem relay_trunk_number (e : End₀) :
    directed total_ true (stemSlots (cfg).toShape (A).cap)=
    (Roster.addr A₁ ord₁ (blocks B) (site e) (localRoster B (site e)) (relayTrunkFace B e)).val+1 :=by
  let face:=relayTrunkFace B e
  let parent:=Roster.resident A₁ ord₁ (blocks B) (site e) face
  have held:=trunk_number B (site e) (land e) parent.property
  have equal : parent=⟨trunk e,parent.property⟩:=Subtype.ext rfl
  rw [←equal] at held
  rw [←directed_addr B]
  change directed total_ true (stemSlots (cfg).toShape (A).cap)=directed (totalLocal B) true _
  rw [show total_ =totalLocal B from fallback_stride B,
    show stemSlots (cfg).toShape (A).cap=stemsCount B from fallback_stems B,←held]

theorem relay_stem_number (e : End₀) :
    directed total_ false (2^rr*(2*(A).cap)+(incomingIndex B e).val)=
    (Roster.addr A₁ ord₁ (blocks B) (site e) (localRoster B (site e)) (relayStemFace B e)).val+1 :=by
  let face:=relayStemFace B e
  let parent:=Roster.resident A₁ ord₁ (blocks B) (site e) face
  have held:=stem_number B (site e) true e parent.property
  have equal : parent=⟨inputStem e,parent.property⟩:=Subtype.ext rfl
  rw [←equal] at held
  rw [←directed_addr B]
  change directed total_ false _=directed (totalLocal B) false ((localRoster B (site e)) parent).val
  rw [show total_ =totalLocal B from fallback_stride B,held]
  congr 1
  simp [incomingIndex,finProdFinEquiv_apply_val,B.keyWidth,Nat.add_comm,show (finTwoEquiv.symm true).val=1 from rfl]

def reached_relay_trunk_socket (e : End₀) (j : Fin split) :
    PublicSocket B (site e) split (earlierIncoming B e*split+j.val) ((T).code (land e)).2.2.isSome
      (directed total_ true (stemSlots (cfg).toShape (A).cap)) :=by
  refine ⟨relayTrunkFace B e,relay_trunk_number B e,?_,Or.inl (trunk_mark B (land e))⟩
  rw [Nat.add_comm,Nat.add_mul_div_right _ _ (Nat.zero_lt_of_lt j.isLt),
    Nat.div_eq_of_lt j.isLt,Nat.zero_add]
  exact incoming_before_end B e

def reached_relay_stem_socket (e : End₀) (j : Fin split) :
    PublicSocket B (site e) split j.val false (directed total_ false (2^rr*(2*(A).cap)+(incomingIndex B e).val)) :=
  ⟨relayStemFace B e,relay_stem_number B e,by rw [Nat.div_eq_of_lt j.isLt];exact (relayStemFace B e).property.1,
    Or.inr j.isLt⟩

/-- Both published columns address the same incident and p-word as the installed
two-row relay. This also fixes the marker for a relay whose trunk is unmarked. -/
theorem reached_relay_request (e : End₀) (arg : Fin (2*split))
    (row : (pubCfg).Data (Z).n) (shape : ↥(DescentDenseHostOrder.roster (Z).graph rr height))
    (live : ((cfg).header ((pubCfg).basic row) 0).val≠0)
    (shapeAt : ((cfg).header ((pubCfg).basic row) 2).val=(localRank (Z).graph rr height shape).val)
    (kind : shape.val=.trunk true ((),(DescentRelativeContacts.shortName (T).commonDepth ((T).code (land e))).2))
    (capAt : ((cfg).header ((pubCfg).basic row) 1).val=(A).cap)
    (sameBatch : batches=split) (j₀ : Fin (cfg).count) (location : j₀.val=(incomingIndex B e).val)
    (chosen : DescentFallbackItemSelect.select ((cfg).relayItems ((pubCfg).basic row))
      ((cfg).relayRows ((pubCfg).basic row) (DescentRelativeContacts.shortName (T).commonDepth ((T).code (land e))).2)
      (earlierIncoming B e)=some j₀) :
    let side:=arg.val<split
    let edge:=if side then trunk e else inputStem e
    let word:=if side then earlierIncoming B e*split+arg.val else arg.val-split
    let mark:=if side then ((T).code (land e)).2.2.isSome else false
    ∃number,∃socket:PublicSocket B (site e) split word mark number,socket.face.val.1=edge ∧
      socket.face.val.2=decide side ∧
      (pubCfg).mixed (Z).graph (earlierIncoming B e) arg.val row=some (number,word,1,mark) :=by
  subst batches
  dsimp only
  have actual:=(publicOperandConfig B field query lanes split split nodes args grain).relay_request (Z).graph row shape live shapeAt kind (earlierIncoming B e) arg.val j₀ chosen arg.isLt
  dsimp only at actual
  have batchSize : (publicOperandConfig B field query lanes split split nodes args grain).batches = split := rfl
  have shapeConfig : (publicOperandConfig B field query lanes split split nodes args grain).toShape =
      (flatConfig B field query lanes split split nodes args).toShape := rfl
  change ((publicOperandConfig B field query lanes split split nodes args grain).header
      ((publicOperandConfig B field query lanes split split nodes args grain).basic row) 1).val = input.placement.cap at capAt
  by_cases low : arg.val<split
  · let s:=reached_relay_trunk_socket (field:=field) (query:=query) (lanes:=lanes) (batches:=split)
      (nodes:=nodes) (args:=args) B e ⟨arg.val,low⟩
    simp only [ite_eq_left low,decide_eq_true low]
    refine ⟨_,⟨s.face,s.address,?_,?_⟩,rfl,rfl,?_⟩
    · simpa only [ite_eq_left low] using s.inside
    · simpa only [ite_eq_left low] using s.mark
    · simp only [batchSize,capAt,shapeConfig,ite_eq_left low] at actual
      exact actual
  · let high : Fin split:=⟨arg.val-split,by have h:=arg.isLt;omega⟩
    let s:=reached_relay_stem_socket (field:=field) (query:=query) (lanes:=lanes) (batches:=split)
      (nodes:=nodes) (args:=args) B e high
    simp only [ite_eq_right low,decide_eq_false low]
    refine ⟨_,⟨s.face,s.address,?_,?_⟩,rfl,rfl,?_⟩
    · simpa only [ite_eq_right low] using s.inside
    · simpa only [ite_eq_right low] using s.mark
    · simp only [batchSize,capAt,shapeConfig,ite_eq_right low,location] at actual
      exact actual


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

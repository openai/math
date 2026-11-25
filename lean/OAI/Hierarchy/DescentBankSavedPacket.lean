import OAI.Hierarchy.DescentRelaySavedPacket
import OAI.Hierarchy.DescentMeasuredBankBadge

namespace OAI
/-! # The saved old packet at a real reblocked bank site -/
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
local notation "wireKey" => DescentOrderedReset.grains W B.count B.order


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
local notation "Face" u:arg => Roster.Face A₁ ord₁ (blocks B) u



variable {field query lanes batches split nodes args grain : ℕ}
local notation "cfg" => flatConfig B field query lanes batches split nodes args
open DescentPackedRotorMatrix DescentResetPublicOperandBook DescentRotorOperandQueryROM.Shape
local notation "cell" s:arg g:arg => DescentChosenRouter.Cells (placement) s g
local notation "atEnd" e:arg s:arg => (if s then (blocks B).dst e else (blocks B).src e)
local notation "landing" => localAddress A before S input.valid digitsIn B.frame.basis

local notation "pubCfg" => publicOperandConfig B field query lanes batches split nodes args grain


open DescentOperandStateBanks DescentResetOperandComponents DescentOperandCandidateLookup
open DescentDatedAddressBook.ResetOutput


local notation "End₀" => (old).graph.Edge
local notation "land" e:arg => (T).home ((old).graph.dst e)
local notation "trunk" e:arg => trunkParent B (land e)
local notation "site" e:arg => (blocks B).dst (trunk e)
local notation "inputStem" e:arg => stemParent B (true,e)
local notation "total_" => total (cfg).toShape (A).cap


open DescentMeasuredOperandKey DescentRelativeContacts DescentSharedBookScan DescentFallbackItemSelect
open DescentDenseHostOrder DescentPacking

open DescentPaidResidentCount.Reset DescentFallbackPeriod DescentStageEdgeReceipt
open DescentOrdinaryAtomFieldRAM
variable {H newH oldBits «fields» N groups₀ fine₀ : ℕ}
    (oldFits:Fintype.card input.V≤H) (newFits:Fintype.card B.next.V≤newH)
    (positive:0<H)
local notation "vertex_" => input.vertex.trans (Fin.castLEEmb oldFits)
local notation "rank_" => B.frame.host.symm.toEmbedding.trans vertex_
local notation "saved_" => PaddedSnapshot B oldFits field
local notation "ranks_" t:arg => DescentSharedBookScan.ranks (a:=rr) («Y»:=2^(Z).n) (D:=(A).degree)
  (t).chart (2^height) (height+2) (t).memory
local notation "input_" => DescentFallbackPeriod.Input (A).degree (2^(m-c)) (A).cap (Z).n rr
local notation "count_" => DescentFallbackPeriod.inputCount (A).degree (2^(m-c)) (A).cap (Z).n rr

local notation "bankSite" b₀:arg => DescentSharedCableNames.Stage.home B.next.placement (B.reblock.destination (((Z).resetNames T).symm (.inr b₀)))

theorem bank_root_at (b₀ : (Z).bank.Site) : receiverRoot B (bankSite b₀)=
    ((Z).rootVertex T b₀.1.2,(Z).rootBlock T b₀.1.2) :=by
  let a₀ := ((Z).resetNames T).symm (.inr b₀)
  exact (congrArg (receiverRoot B) (named_home B a₀)).trans
    ((receiverRoot_site B a₀).trans (root_at_bank_site B b₀))

open DescentResetStemCompactOrder DescentResetStemWord

theorem bank_self_word (b₀ : (Z).bank.Site) :
    let v₀:=B.frame.host.symm ((Z).rootVertex T b₀.1.2)
    stemSelfDigit B (originalTrunkRack B) (((denseOrder B) (bankSite b₀).1.2).castLE newFits)=
      DescentResetStemWord.hostCode (compress (hostDomain
        (A) input.vertex v₀) (input.vertex v₀).val) (decide (v₀∉(A).near v₀)) :=by
  let u:=(bankSite b₀).1.2
  let h:=((denseOrder B) u).castLE newFits
  have live : h.val<Fintype.card B.next.V:=((denseOrder B) u).isLt
  have stored : originalTrunkRack B h=some u:=by
    rw [originalTrunkRack,dite_eq_left live]
    exact congrArg some ((denseOrder B).symm_apply_apply u)
  have earlier:=congrArg Prod.fst (bank_root_at B b₀)
  change position (Z).graph u.val=(Z).rootVertex T b₀.1.2 at earlier
  change stemSelfDigit B (originalTrunkRack B) h = _
  unfold stemSelfDigit
  rw [stored]
  simp only [Option.elim_some,stemOldHost,earlier]

theorem bank_coarse_block (b₀ : (Z).bank.Site) :
    (bankSite b₀).1.1.val*2^k+(bankSite b₀).2.val=((Z).rootBlock T b₀.1.2).val:=by
  have eq:=congrArg (fun x=>x.2.val) (bank_root_at B b₀)
  change (bankSite b₀).2.val+2^k*(bankSite b₀).1.1.val=_ at eq
  exact ((Nat.add_comm _ _).trans (congrArg _ (Nat.mul_comm _ _))).trans eq

theorem bank_packet_address (b₀:(Z).bank.Site)
    (groupsAt:groups₀=S.groupCount (i+1)) (blocksAt:fine₀=2^k) (groupAt:groups₀*fine₀=2^c):
    (Z).packetOwner T rank_ positive (((denseOrder B) (bankSite b₀).1.2).castLE newFits)=
        vertex_ (B.frame.host.symm ((Z).rootVertex T b₀.1.2)) ∧
      (finProdFinEquiv ((bankSite b₀).1.1.cast groupsAt.symm,(bankSite b₀).2.cast blocksAt.symm)).cast groupAt=
        (Z).rootBlock T b₀.1.2:=by
  have root:=bank_root_at B b₀
  have oldRoot:=congrArg Prod.fst root
  have blockRoot:=congrArg Prod.snd root
  constructor
  · let h:=((denseOrder B) (bankSite b₀).1.2).castLE newFits
    have live : h.val<Fintype.card B.next.V:=((denseOrder B) (bankSite b₀).1.2).isLt
    have held:originalTrunkRack B h=some (bankSite b₀).1.2:=by
      rw [originalTrunkRack,dite_eq_left live]
      exact congrArg some ((denseOrder B).symm_apply_apply _)
    have numbered:=(calibrated_rack B oldFits h (bankSite b₀).1.2 held).2.1
    apply Fin.ext
    change (if h₀:h.val<Fintype.card B.next.V then (Z).parentIndex T rank_ ⟨h.val,h₀⟩ else ⟨0,positive⟩).val=_
    rw [dite_eq_left live]
    exact numbered.trans (congrArg (fun t=>(vertex_ (B.frame.host.symm t)).val) oldRoot)
  · subst groups₀;subst fine₀
    apply Fin.ext
    exact (show (finProdFinEquiv ((bankSite b₀).1.1,(bankSite b₀).2)).val=((digits).symm ((bankSite b₀).1.1,(bankSite b₀).2)).val from rfl).trans
      (congrArg Fin.val blockRoot)

theorem bank_saved_packet (snap:saved_) (b₀:(Z).bank.Site)
    (groupsAt:groups₀=S.groupCount (i+1)) (blocksAt:fine₀=2^k) (groupAt:groups₀*fine₀=2^c)
    (bitsAt:oldBits=field) (fieldsAt:«fields»=count_)
    (orig:Fin H→Fin (groups₀*fine₀)→Cell (oldBits*«fields»))
    (stored:∀r j,(orig r j).val=(savedInput B oldFits snap r (j.cast groupAt)).val) (key:input_):
    let who:=(Z).packetOwner T rank_ positive (((denseOrder B) (bankSite b₀).1.2).castLE newFits)
    let j:=finProdFinEquiv ((bankSite b₀).1.1.cast groupsAt.symm,(bankSite b₀).2.cast blocksAt.symm)
    (((DescentSIMDLookup.encode oldBits «fields»).symm (orig who j)) ((DescentFallbackPeriod.number key).cast fieldsAt.symm)).val=
      ((DescentFallbackPeriod.inputs (field:=field) snap.stencil snap.peers snap.marks
        (fun u l=>((ranks_ snap) u l).val) (vertex_ (B.frame.host.symm ((Z).rootVertex T b₀.1.2)))
          ((Z).rootBlock T b₀.1.2)) key).val:=by
  subst oldBits;subst «fields»
  intro who j
  have source:=stored who j
  obtain ⟨oldHost,oldGroup⟩:=bank_packet_address B oldFits newFits positive b₀ groupsAt blocksAt groupAt
  have original : orig who j=snap.packed (vertex_ (B.frame.host.symm ((Z).rootVertex T b₀.1.2)))
      ((Z).rootBlock T b₀.1.2) :=by
    apply Fin.ext
    apply source.trans
    change (snap.packed who (j.cast groupAt)).val=_
    rw [show who=vertex_ (B.frame.host.symm ((Z).rootVertex T b₀.1.2)) from oldHost,
      show j.cast groupAt=(Z).rootBlock T b₀.1.2 from oldGroup]
  change (DescentFallbackPeriod.packet (orig who j) key).val=_
  rw [original]
  exact congrArg Fin.val (congrFun (DescentFallbackPeriod.packet_encode _) key)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI

import OAI.Hierarchy.DescentRecordedRetainedTicket
import OAI.Hierarchy.DescentOriginalPacketTrunk

namespace OAI
/-! # Both retained correction sources on the named calendar reset -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentActorRaster DescentPackedZip DescentPackedColony DescentColonies
open scoped Classical Fin.CommRing
variable {F X : Type} [Field F] {d : ℕ} {abits : X→ℕ} {W : MarkedWorld F d X abits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age z wire hist D n h C f g cut tail p : ℕ}
  {input : Reached W G q ε S k age z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  {B : ClosedReset input ctl} (accepted : B.Recorded p)
local notation "board" => ctl.board
local notation "packet" => ctl.bitsR
variable (drift degree payload e previous M nextM oldLanes primitiveLanes printedBits : ℕ)
  (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor w : ℕ)
local notation "a" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "v" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤wide-k) (fitsSigned : e≤previous) (fitsCut : previous≤cc) (count : Bank)
local notation "sh" => namedStencil G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsStencil
local notation "roots" => namedRoots G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut
local notation "atlas" => namedAtlas G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor sh count
local notation "rc" => (a).rootPhase sh start count io.hubs g (2^n) roots w
local notation "P" => (a).stencilPhase sh start count io.hubs g (2^n)
local notation "E" => (a).estimator start
local notation "book" => atlasBook atlas sh start count io.hubs g (2^n) roots w
local notation "actorBase" => (v).middle.stop base₀
local notation "early" => (v).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : (rc).PreparedFits book)
  (sceneRoom : (v).front.SceneRoom early ((v).issuedScene base₀ older) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom

open DescentResetLocalRoster DescentSixParty.ClosedReset.Window

open DescentResetSourceTicketCompare DescentResetTrunkCompactPointer DescentResetFieldAssembler
open scoped BigOperators

local notation "A₁" => (v).receiver
local notation "F₀" => (v).front
local notation "C₀" => (v).setup
local notation "H₀" => S.hostSize age
local notation "H₁" => S.hostSize (age+1)
local notation "G₁" => S.groupCount (age+1)
local notation "keyWidth" => originalBits D k n (GroupStage.depthBound D n f g)
  input.placement.cap (programCount board (GroupStage.depthBound D n f g)) g
local notation "rank₀" => B.frame.host.symm.toEmbedding.trans (input.vertex.trans (Fin.castLEEmb input.valid.host))
local notation "dense₀" => (B.reset.denseHostRank B.terminals rank₀).trans (Fin.castLEEmb B.next.valid.host)
local notation "rack₀" => rackOf B dense₀
local notation "st" => (v).sheetsStart base₀
local notation:max "FEE" x:arg j:arg h:arg gr:arg => ∑l,feeAt (wordBefore B) (original_fees (b:=keyWidth) B rack₀ x h gr) j l
local notation "first₀" => (v).operandFloor base₀
local notation:max "dst" ok:arg m:arg => ((C₀).code first₀ w (u).bank (u).laws).image ((u).beforeSetupImage ok m)

private theorem retained_prefix_cast {β : Type} {b c : ℕ} (site : Option β)
    (num : β→ℕ) (small : ∀z₀,num z₀<2^b) :
    (((site.elim (0:Cell b) (fun y=>(num y:Cell b))).val:ℕ):Cell c)=
      ((site.elim 0 num:ℕ):Cell c):=by
  cases site with
  | none => simp
  | some y => simp only [Option.elim_some,Fin.val_natCast,Nat.mod_eq_of_lt (small y)]

set_option maxHeartbeats 1000000 in
/-- The physical compact source on each retained input and the old hub
flag are read in the same final memory as the selected operand dictionaries. -/
theorem DateInputs.fromNamed_retained_controls (degreeAt : venue.degree=D) (paid : input.placement.cap=cap)
    (ok : (u).Ready) (m : Memory w)
    (earned : ActorTrunkReads B input.valid.host (F₀) ((v).actorEnd base₀)
      ((v).issuedScene base₀ (u).earlier) (u).sceneFits m)
    (src : RankSources B (b:=(v).sheets.metaBits) (t:=keyWidth) (M:=(v).sheets.lanes) rack₀
      ((v).rankPorts base₀) (sheetHeader B st (u).sectors.pageBits) (sheetOriginal B st (u).sectors.pageBits)
      (((v).rankPortPhase base₀ w).image ((u).before_ports ok m)))
    :
    ∃(slotAt : Fin (C₀).strip→Fin (totalLocal B))
     (hub : Fin H₁→Fin G₁→Cell (C₀).fieldBits)
     (fee : Fin (2^k)→Fin (C₀).strip→Fin H₁→Fin G₁→Cell (C₀).fieldBits),
      (∀j,(slotAt j).val=2^k*(2*input.placement.cap)+j.val) ∧
      (∀h gr,hub h gr=if ((originalTrunkRack B h).elim .blank (hostShape B)).core then 0 else 1) ∧
      (∀x j h gr,fee x j h gr=(((pointer B.next.valid.host (compactTrunkPeer B input.valid.host) h).elim 0
        (fun h₀=>FEE x (slotAt j) h₀ gr):ℕ):Cell (C₀).fieldBits)) ∧
      (∀x,((v).retainedHub base₀ x).Fits w ((C₀).casts first₀) ∧
        Source ((v).retainedHub base₀ x) hub M (dst ok m)) ∧
      (∀x j,((v).retainedTicket base₀ x j).Fits w ((C₀).casts first₀) ∧
        Source ((v).retainedTicket base₀ x j) (fee x j) M (dst ok m)) :=by
  obtain ⟨hx,hj,gg,hosts,lanes,«meta»,key,before,gate,capa,deg,fit⟩:=
    fromNamed_rank_coordinates (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
      printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial
      prepared sceneRoom degreeAt paid
  have positive : 0<M:=ok.placed.lanes
  have small {k₀ : ℕ} (bound : 2^k₀<2^w) : k₀≤w:=by
    by_contra! bad
    exact (not_le_of_gt bound) (Nat.pow_le_pow_right (by decide : 0<2) bad.le)
  have cuts:=(v).control_address_bounds base₀
  have toCtl : (v).rankEnd base₀≤(v).controlFloor base₀ :=
    (Nat.le_add_right _ _).trans (((v).receiver.occupied ((v).fieldsEnd base₀)).1)
  have rankSpace:=((toCtl.trans cuts.2.2.1).trans cuts.2.2.2).trans_lt ok.full
  have pairSpace : (v).pairEnd base₀≤(v).ticketEnd base₀:=by
    exact ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)).trans (Nat.le_add_right _ _)
  have bound:=(pairSpace.trans ((v).earlier base₀).2.1).trans_lt rankSpace
  have tab : 2^(((v).assemblerBits*7+(v).ticketBits)*M)≤(v).pairEnd base₀:=by
    change _≤(v).rankPortEnd base₀+6*2^(((v).assemblerBits*7+(v).ticketBits)*M)
    omega
  have stamp : ((F₀).metaBits*7)*M≤w:=
    (Nat.mul_le_mul_right M (Nat.le_add_right ((v).assemblerBits*7) ((v).ticketBits))).trans
      (small (tab.trans_lt bound))
  have clocks:=(v).operand_order base₀
  have stay : (v).operandStart base₀<2^w:=
    (clocks.1.trans (clocks.2.trans ((v).final_ge base₀))).trans_lt ok.full
  have table : 2^((C₀).fieldBits*M)≤(v).operandStart base₀:=by
    change _≤(v).keepBase base₀+1*(2*2^((C₀).fieldBits*M))
    omega
  have packing:=small (table.trans_lt stay)
  have nDonor : (C₀).retained.donors=2^k:=by
    let ex:=S.retainedExponent G k tail drift degree p age payload
    have low : ex≤cc:=Nat.min_le_left ..
    change 2^(cc-ex+(ex+k)-cc)=2^k
    congr 1
    omega
  have aperture : (C₀).strip=2^k*(2*cap):= congrArg (·*(2*cap)) nDonor
  have signed : (F₀).signedQueries=2*(2^k*(2*cap)):=rfl
  have startAt : (F₀).signedQueries/2=2^k*(2*cap):=by rw [signed];omega
  have count_ : (A₁).candidates=2*(2^k*(2*cap))+
      (1+(2*(rootSlots k (2^n)*(2^n+2^Ht))+2*(rootSlots k (2^n)*(DescentResetCableSlots.cableCap board Ht)))):=rfl
  have jRoom (j : Fin (C₀).strip) : (F₀).signedQueries/2+j.val<(A₁).candidates:=by
    have lim : j.val<2^k*(2*cap) := j.isLt.trans_le aperture.le
    rw [startAt,count_];omega
  let sel (j : Fin (C₀).strip) : Fin (totalLocal B):=Fin.cast hj ⟨_,jRoom j⟩
  let hub (h : Fin H₁) (_ : Fin G₁) : Cell (C₀).fieldBits:=
    if ((originalTrunkRack B h).elim .blank (hostShape B)).core then 0 else 1
  let other:=compactTrunkPeer B input.valid.host
  let fee (x : Fin (2^k)) (j : Fin (C₀).strip) (h : Fin H₁) (gr : Fin G₁) : Cell (C₀).fieldBits:=
    ((pointer B.next.valid.host other h).elim 0 (fun h₀=>FEE x (sel j) h₀ gr):ℕ)
  refine ⟨sel,hub,fee,fun j=>?_,fun _ _=>rfl,fun _ _ _ _=>rfl,?_,?_⟩
  · change (F₀).signedQueries/2+j.val=_
    rw [startAt,paid]
  · intro x
    have pos : 0<(F₀).metaBits:=by
      change 0<CandidateFront.endpointWidth venue.degree _ (2^g*cap)
      apply lt_of_lt_of_le _ (Nat.le_max_left _ _)
      exact Nat.clog_pos (by decide) ((by decide : 1<5).trans_le (Nat.le_max_left ..))
    exact dated_primary_hub B (u) ok m x rfl positive pos stamp packing earned.1
  · intro x j
    let addr:=(B.reset.rawHostRank B.terminals rank₀)
    let R:=H₀*(DescentDenseHostOrder.roster B.reset.graph (B.reset.k-B.terminals.commonDepth) (GroupStage.depthBound D n f g)).card
    have hostsAt : R=(F₀).peer.hosts:=by
      change R=H₀*(DescentDenseHostOrder.roster board k Ht).card
      rw [degreeAt];exact congrArg (H₀*·) (calendar_palette B).symm
    have paidSize : Fintype.card B.next.V≤R:=by
      simpa only [Fintype.card_fin] using Fintype.card_le_of_injective (fun node : B.next.V => addr node) addr.injective
    have inv : Fintype.card B.next.V≤((v).issuedScene base₀ (u).earlier).inverse.size:=by
      apply paidSize.trans
      rw [hostsAt]
      exact Nat.le_pow_clog (by decide) _
    let retyped:=rank_sources_at B hosts lanes «meta» key rack₀ ((v).rankPorts base₀)
      (((v).rankPortPhase base₀ w).image ((u).candidateEntry ok m)) src
    have got:=recorded_ticket_at B (u) hx hj gg before gate _ ok m retyped rfl jRoom rfl rfl rfl rfl rfl
      hostsAt (compactActorName B input.valid.host) other B.next.valid.host inv earned.2 x j
    refine ⟨got.1,?_⟩
    let rawFee (h : Fin H₁) (gr : Fin G₁) : Cell (C₀).fieldBits :=
      (((pointer B.next.valid.host other h).elim (0:Cell (v).assemblerBits) (fun h₀=>
        ((∑l,feeAt (wordBefore B) (original_fees (b:=(v).ticketBits) B rack₀ x h₀ gr) (sel j) l:ℕ):
          Cell (v).assemblerBits))).val:Cell (C₀).fieldBits)
    have original : Source ((v).retainedTicket base₀ x j) rawFee M (dst ok m):=got.2
    have numeric : rawFee=fee x j:=by
      funext h gr
      unfold rawFee fee
      rw [key]
      apply retained_prefix_cast
      intro r
      exact (sum_fee_le (b:=keyWidth) B rack₀ x r gr (sel j)).trans_lt
        (((Nat.le_succ _).trans (Nat.le_max_right _ _)).trans_lt fit)
    simpa only [numeric] using original

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI

import OAI.Hierarchy.DescentNamedMatrixPorts
import OAI.Hierarchy.DescentNamedRootSigned
import OAI.Hierarchy.DescentIndexedCalendarPacket
import OAI.Hierarchy.DescentPhysicalRootSpectra
import OAI.Hierarchy.DescentNamedActorReady
import OAI.Hierarchy.DescentPhysicalResetDateOutput

namespace OAI
/-! # The original matrix and four header tables at the reached named reset date -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM DescentSixParty.PackedFlow DescentPlainTerminal.Suffix
noncomputable section
set_option quotPrecheck false
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
local notation "successor₀" => (a).successor
local notation "start" => (a).stageStart floor
local notation "base₀" => (a).rebased start
local notation "cc" => S.groupWidth k tail age
local notation "cal" => capCalendar G.b S.rounds g S.height
local notation "cap" => ((cal).take age).prod*256
local notation "Ht" => GroupStage.depthBound venue.degree n f g
local notation "wide" => laneBits (cc+k) payload (S.localWalshBits p (cc+k) f (quota S.rounds))
variable (fitsStencil : e≤(laneBits ((S.groupWidth k tail age)+k) payload (S.localWalshBits p ((S.groupWidth k tail age)+k) f (quota S.rounds)))-k) (fitsSigned : e≤previous) (fitsCut : previous≤(S.groupWidth k tail age)) (count : Bank)
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
local notation "actorBase" => (successor₀).middle.stop base₀
local notation "early" => (successor₀).actorEnd base₀

local notation "older" => namedOriginals G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
local notation "I₀" => DateInputs.fromNamed G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count
variable (previousMeta previousArguments : ℕ) (initial : Bool) (prepared : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rootPhase (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w)).PreparedFits (atlasBook (namedAtlas G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) count) (namedStencil G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsStencil) (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor) count io.hubs g (2^n) (namedRoots G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor fitsSigned fitsCut) w))
  (sceneRoom : ((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).front.SceneRoom (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).actorEnd (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor))) (((((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).successor)).issuedScene (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).rebased (((named G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor)).stageStart floor)) (namedOriginals G S (ctl.board) k tail age p f g drift degree payload e previous M nextM C (ctl.bitsR)
  oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count)) w)
local notation "u" => I₀ previousMeta previousArguments initial prepared sceneRoom
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "idx" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "rank" => B.frame.host.symm.toEmbedding.trans idx
local notation "rawId" => (Z).rawHostRank T rank
local notation "HH" => S.hostSize age
local notation "nBits" => k+S.localWalshBits p (cc+k) f (quota S.rounds)+2
local notation "tBits" => 2*k+n+2
local notation "amp" => input.placement.wire*(input.placement.z*G.b)*input.placement.cap

open DescentFallbackPeriod.Projected DescentPaidResidentCount.Reset
local notation "sources" => atlasSender atlas sh start count io.hubs g (2^n) roots w
local notation "middle" => (successor₀).middle
open DescentGL DescentGroupPeerOrder DescentFallbackRankRAM
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=((((capCalendar G.b S.rounds g S.height)).take age).prod*256))
local notation "fac" => 32*Nat.clog 2 (2*venue.degree)
local notation "staged" => fromNamed_matrix_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "im" => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "pg" => ((false,.inr (⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le k) (by decide)⟩,none)) : DescentSixParty.Chronology.RootPage k (2^n))
local notation "deck" => Receiver.IssuedDeck.mk (atlas).directions (atlas).board (atlas).primitive pg
local notation "menu" => (deck).reindex (degreeAt.trans input.branch.symm) rfl
  (show k=(cc-e+(e+k))-(T).commonDepth by rw [B.commonDepth];omega)
local notation "field" => (successor₀).middle.rootField
local notation "len" => cc-e+(e+k)

private theorem basis_cast {d₀ d₁ : ℕ} (eqn : d₀=d₁) (μ : DescentGL.Layout d₀) :
    HEq (cast (congrArg DescentGL.Layout eqn) μ) μ :=by cases eqn;rfl

private theorem order_cast {d₀ d₁ ww : ℕ} (eqn : d₀=d₁) (μ : DescentGL.Layout d₀) (st : StencilBook)
    (old : StencilBook.Sources) (b o g c : ℕ) (m : Memory ww) (seen : st.OldOrder old b o g c μ m) :
    st.OldOrder old b o g c (cast (congrArg DescentGL.Layout eqn) μ) m :=by cases eqn;exact seen

set_option maxHeartbeats 500000 in
include accepted in
/-- The actual measured memory supplies all original matrix rows at this date and its four root headers. -/
theorem DateInputs.fromNamed_calendar_root_packet (ready : (u).Ready) (mem measured : Memory w)
    (gr : z=S.grainAt G.b p (age+1)) (fee : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain)
    (seen : stageVenue input input.valid.host io (successor₀).funded.oldLanes (successor₀).funded.precision floor
      (input.venueRoster input.valid.host) mem)
    (wireRoom : ∀(x : DescentColonies.Block k)(j : Fin (2*input.placement.cap)),(io.wire x.val j.val).Fits w floor ∧
      HH*chunks (S.groupCount age) (successor₀).funded.oldLanes≤(io.wire x.val j.val).size)
    (hubs : HH≤ io.hubs.size) (hosts : HH<2^w) (degFit : venue.degree+1<2^w)
    (names : DescentFallbackShapeTable.actorWordBits k fac g n≤w)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(successor₀).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w) (capacity : venue.cap=cap)
    (pitchOld : venue.lanes=2^previous)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (headerBits : Nat.clog 2 ((E).dim+2)+((E).dim+S.censusBits p)≤w)
    (live : 0<amp) (degreePos : 0<fac)
    (μ : DescentGL.Layout (E).dim) (won : HEq μ B.frame.basis)
    (saved : measured (P).saved=((DescentExterior.matrixCode μ).val:Word w))
    (kept : ∀x<floor,measured x=mem x)
    (reserved : ClosedReset.Recorded.StencilReservationWords (reset:=B) E
      ((sh).dimension.symm.trans B.keyWidth.symm) venue.degree degreeAt.symm.le measured)
    (order : (P).S.OldOrder (P).X (P).base (P).bank g (T).commonDepth μ measured)
    (panel : ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
      count (E).depthRows (rc).stencil book measured) :
    ∃hdr : OriginalHeader B input.valid.host (im).receiver (im).book measured,
    ∃x : OriginalArrays B input.valid.host field,
      ClosedReset.Window.RootPacket B (im).receiver (im).book (im).prepared measured hdr (im).sources x nBits tBits :=by
  have dim : (E).dim=cc+k :=(sh).dimension.symm
  have num : len=(E).dim :=by rw [dim]; omega
  have width : (E).dim=(Z).k:=dim.trans B.keyWidth.symm
  have residual : (E).dim-(T).commonDepth=k :=by rw [dim,B.commonDepth];omega
  have fieldPaid :=fromNamed_matrix_packing G S board k tail age p f g drift degree payload e previous M nextM C packet
    oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count chosen pitch small word ceiling capacity
  have hfield : Ht+2≤field:=fieldPaid.2.2
  have countPos : 0<DescentRotorWindowArchive.count venue.degree (2^k) venue.cap :=by
    unfold DescentRotorWindowArchive.count
    positivity
  have fw : field≤w:=by
    have bound:=fieldPaid.1
    have p₀:=Nat.le_mul_of_pos_right field countPos
    have p₁:=Nat.le_mul_of_pos_left (max (field*DescentRotorWindowArchive.count venue.degree (2^k) venue.cap)
      (DescentRotorWindowArchive.output n (2^k) venue.cap)) (Nat.two_pow_pos e)
    omega
  have orig:=DateInputs.fromNamed_original_header (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
    printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared
    sceneRoom degreeAt capAt ready measured panel hubs hosts degFit names chosen pitch small word ceiling capacity (hfield.trans fw)
  refine ⟨orig,?_⟩
  have target:=fromNamed_matrix_target (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
  have state:=fromNamed_matrix_state (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt measured
  obtain ⟨prev,key⟩:=DateInputs.fromNamed_root_signed (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt mem measured
    μ saved kept seen wireRoom pitchOld num.symm
  obtain ⟨mounted,accessible,ident⟩:=DateInputs.fromNamed_reached_ports (B:=B) drift degree payload e previous M
    nextM oldLanes primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta
    previousArguments initial prepared sceneRoom degreeAt capAt ready mem measured seen kept μ order
  have area:=fromNamed_matrix_area (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments initial prepared sceneRoom
    degreeAt capAt ready chosen pitch small word ceiling
  have same:=fromNamed_matrix_issued (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
  have full : (a).fullBudget=wire*(z*G.b)*input.placement.cap :=by
    change S.epochPower^S.priceExponent*(S.grainAt G.b p (age+1)*G.b)*cap=_
    exact congrArg₂ Nat.mul (congrArg₂ Nat.mul fee.symm (congrArg (· * G.b) gr.symm)) capAt.symm
  have billed : (P).S.total=(E).dim+S.censusBits p :=by rw [dim]; rfl
  rw [full,billed] at same
  let basis:=cast (congrArg DescentGL.Layout num.symm) μ
  have hit : HEq basis B.frame.basis:=(basis_cast num.symm μ).trans won
  have shape:=ClosedReset.real_panel_width B (M:=2^e) (t:=tBits) (nbits:=nBits) (num.trans dim) basis hit
    (rc).stencil.base measured panel.panel
  have order' :=order_cast num.symm μ (P).S (P).X (P).base (P).bank g (T).commonDepth measured order
  have begin : (P).base≤(rc).origin := ((P).S.banks (P).X (P).base (P).bank ready.stencil.operands).2.2.2.2.2.2.2.2.trans
    ((P).S.header_before_output (P).base)
  have after : (E).endAddress≤(rc).origin :=by
    have first : (E).endAddress≤(P).fresh:=(((a).chart start).estimator_range (a).payload (a).gain (a).positive).2.2
    have next : (P).fresh≤(P).first:=by unfold PackedFlow.ResetMiddle.first PackedFlow.ResetMiddle.saved;omega
    have last : (P).first≤(P).base:=by unfold PackedFlow.ResetMiddle.base Subwords.finish Subwords.destination;omega
    exact first.trans (next.trans (last.trans begin))
  obtain ⟨l₁,l₂,l₃⟩:=(book).limits (rc).projectionEnd HH (2^cc) (2^e)
  have top : (P).endAddress≤(rc).headerEnd book:=(rc).origin_le_projection.trans (l₁.trans (l₂.trans l₃))
  have spectra:=(a).root_spectra_fit sh start count io.hubs g (2^n) ready.prime.fit _ top
  have shapeStop : (rc).stencil.base+HH*chunks (2^(T).commonDepth) (2^e)≤(rc).origin:=by
    rw [B.commonDepth]
    change (P).S.output (P).base+(P).S.rows≤(P).S.endAddress (P).base
    exact ((P).S.output_end (P).base).ge
  have shapeRows : HH*chunks (2^(T).commonDepth) (2^e)≤(rc).stencil.size :=by
    rw [B.commonDepth];exact Nat.le_pow_clog (by decide) _
  have beforeKey : (rc).saved.Fits w (rc).origin :=
    ⟨prepared.key.1,prepared.key.2.1,(Nat.succ_le_of_lt (stencil_saved_before («u»:=u)))⟩
  have enough : input.placement.wire*(input.placement.z*G.b)*input.placement.cap < 2^(S.censusBits p) :=
    (input.placement.census_caps_at S input.valid ctl.height B.age.le
      (input.grain.trans gr) (input.edges.trans fee) branch).2
  have aa : amp=wire*(z*G.b)*input.placement.cap :=by rw [input.edges,input.grain]
  have zeropaid : 0<wire:=by
    by_contra! hz
    have noWire : wire=0:=by omega
    simp only [aa,noWire,Nat.zero_mul,Nat.lt_irrefl] at live
  have powSize : 2^len=S.groupCount age*2^k :=by rw [num,dim,pow_add,S.group_power ctl.base ctl.radix age]
  have split : (T).commonDepth≤len:=by rw [num,dim,B.commonDepth];omega
  have dRoom : (T).commonDepth<2^w :=by
    rw [B.commonDepth]
    exact (show cc≤w by omega).trans_lt Nat.lt_two_pow_self
  have wpos : k<w:=by omega
  have expRoom : 2^((E).dim-(T).commonDepth)<2^w:=by rw [residual]; exact Nat.pow_lt_pow_right (by decide) wpos
  have bound : k<field ∧ n<field ∧ tBits<field:=by
    have paid : ResetMiddle.senderWidth k n Ht cap≤field := by
      change _ ≤ ResetMiddle.fieldWidth venue.degree cap n k Ht
      unfold ResetMiddle.fieldWidth
      exact (le_max_right ..).trans ((le_max_right ..).trans ((le_max_right ..).trans (le_max_right ..)))
    dsimp only [ResetMiddle.senderWidth] at paid
    omega
  have sheet : max (max ((E).dim-(T).commonDepth) (2^n)) (2^((E).dim-(T).commonDepth))<2^field:=by
    rw [residual]
    exact max_lt (max_lt (Nat.lt_two_pow_self.trans (Nat.pow_lt_pow_right (by decide) bound.1))
      (Nat.pow_lt_pow_right (by decide) bound.2.1)) (Nat.pow_lt_pow_right (by decide) bound.1)
  have one : 1<2^nBits:=Nat.one_lt_two_pow (by omega)
  have level : k<2^nBits:=Nat.lt_two_pow_self.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  have usable : S.censusBits p ≤ S.localWalshBits p (cc+k) f (quota S.rounds) :=by
    dsimp only [AtomSchedule.localWalshBits,DescentWalshPrecision.bits];omega
  have mass : 2^k*amp<2^nBits:=calc
    _ < 2^k*2^(S.censusBits p) :=Nat.mul_lt_mul_of_pos_left enough (Nat.two_pow_pos _)
    _ ≤ _ :=by rw [←pow_add];exact Nat.pow_le_pow_right (by decide) (by omega)
  have codes:=DescentFallbackShapeTable.actor_shape_rows k n
  have tagWidth : (successor₀).middle.stencil.t=tBits := by rfl
  have outer:=Receiver.indexed_calendar_packet accepted E staged (P).S (P).X (P).base (P).bank g (menu).peers
    (atlas).hostIndex (.lit ((a).c/2)) venue.degree (menu).board (atlas).packet (atlas).groupDigits (atlas).batches
    (atlas).layerBits (atlas).factor (menu).primitive (menu).page same.1 same.2 width num degreeAt.symm.le measured reserved
    ready.prime.fit (state.1.symm ▸ after) (state.2.2.2.1.symm ▸ spectra.1) (state.2.2.2.1.symm ▸ spectra.2)
    (by omega) headerBits (by dsimp [DescentFallbackShapeTable.actorWordBits] at names;omega) zeropaid (aa ▸ live) enough
    hosts dRoom expRoom sheet basis powSize (pow_add 2 e k) split
    (by rw [num,residual];exact (pow_add 2 e k).symm) prev key
    (by rw [state.1,state.2.1];exact beforeKey) (by rw [state.1,state.2.2.1];exact shapeStop)
    (by rw [state.2.2.1];exact shapeRows) (by rw [state.2.2.1];exact shape) order' rfl rfl
    (by change 0<nBits;omega) (by rw [state.1];rfl) mounted accessible ident
    (by erw [target]; exact orig) area hit bound.2.2
    (by simpa only [B.commonDepth,Nat.add_sub_cancel_left] using level) one
    (by simpa only [B.commonDepth,Nat.add_sub_cancel_left] using mass)
    (by simpa only [B.commonDepth,Nat.add_sub_cancel_left,B.dimension,tagWidth] using codes) live (Nat.succ_pos _)
    (by rw [input.branch,←degreeAt];exact degreePos)
  have resultEq := congrArg (fun z =>
    ∀ hdr : OriginalHeader B input.valid.host z.receiver z.book measured,
      ∃ x : OriginalArrays B input.valid.host field,
        ClosedReset.Window.RootPacket B z.receiver z.book z.prepared measured hdr z.sources x nBits tBits) target
  exact (resultEq.mp (fun _ => outer)) orig

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI

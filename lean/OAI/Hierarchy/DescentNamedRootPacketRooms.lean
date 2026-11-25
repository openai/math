import OAI.Hierarchy.DescentNamedCalendarRootPacket
import OAI.Hierarchy.DescentNamedPrivatePageRooms
import OAI.Hierarchy.DescentPhysicalRootHeaderHeads

namespace OAI
/-! # The projected count, original source depths and private apertures at the same reached root -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty.Chronology DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup
open DescentCommonHost DescentDenseHostOrder DescentFallbackPeriod DescentRecordedRotorLayers
open ProtocolRAM
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
local notation "nextReset₀" => (a).successor
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
local notation "actorBase" => (nextReset₀).middle.stop base₀
local notation "early" => (nextReset₀).actorEnd base₀

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
local notation "inputs₀" => I₀ previousMeta previousArguments initial prepared sceneRoom
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
local notation "middle" => (nextReset₀).middle
open DescentGL DescentGroupPeerOrder DescentFallbackRankRAM
variable (degreeAt : venue.degree=D) (capAt : input.placement.cap=((capCalendar G.b S.rounds g S.height).take age).prod*256)
local notation "fac" => 32*Nat.clog 2 (2*venue.degree)
local notation "staged" => fromNamed_matrix_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
local notation "im" => fromNamed_root_image (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes
  printedBits venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt
open DescentPlainTerminal.Suffix DescentPacking.PackedMatch.Local.Stage.Chooser
local notation "head" => (P).S.header (P).base
local notation "field" => (nextReset₀).middle.rootField
local notation "mid" m₀:arg => (im).receiver.preparedMid (im).book (im).prepared m₀
local notation "ceil" => (im).receiver.headerEnd (im).book
local notation "depths" => ClosedReset.Recorded.oldDepth B
local notation "coarse" => (T).commonDepth
local notation "span" => (Z).k-coarse
local notation "cat" => RootTemplates.arena ceil HH (2^coarse) (2^e) span (Z).n input.placement.degree
local notation "pop" => Fintype.card input.V

/-- Every scalar and every private packet is available on the input and shape used by the original probe. -/
theorem DateInputs.named_root_packet_rooms (ready : (inputs₀).Ready)
    (chosen : e=receiverCut G S board k tail age p f g drift degree payload previous nextM C packet
      oldLanes primitiveLanes printedBits venue) (pitch : M=2^e) (small : 8*(nextReset₀).groupWidth≤payload)
    (word : payload≤w) (ceiling : (a).fullEnd floor<2^w)
    (score : 3*(E).dim+((E).precision+Nat.clog 2 (E).hosts)+2≤w)
    (measured : Memory w) (μ : DescentGL.Layout (E).dim)
    (reservation : ClosedReset.Recorded.StencilReservationWords (reset:=B) E
      ((sh).dimension.symm.trans B.keyWidth.symm) venue.degree degreeAt.symm.le measured)
    (order : (P).S.OldOrder (P).X (P).base (P).bank g coarse μ measured)
    (panel : ClosedReset.Recorded.ActorPanelAt (B:=B) (M:=2^e) (t:=tBits) (nbits:=nBits)
      count (E).depthRows (rc).stencil book measured) (popFit : count.Fits w floor) :
    (head).chart.Resident (mid measured) ∧ (head).depth.Fits w ceil ∧ (P).X.levels.Fits w ceil ∧
    (∀v : Fin HH,v.val<pop→v.val*((P).S.m+1)<(P).X.levels.size) ∧
    (∀v : Fin HH,v.val<pop→(mid measured) ((P).X.levels.base+v.val*((P).S.m+1))=(depths v:Word w)) ∧
    (∀v : Fin HH,v.val<pop→coarse≤depths v ∧ depths v<2^w) ∧
    (∀v : Fin HH,v.val<pop→depths v-coarse+1<2^field) ∧
    (∀p₀ : Row HH (2^coarse) (2^e),(P).X.count.eval (mid measured) ((row _ _ _ p₀).val:Word w)=(pop:Word w)) ∧
    (∀p₀ : Row HH (2^coarse) (2^e),(Expr.lookup (atlas).hostIndex .row).eval (mid measured)
      ((row _ _ _ p₀).val:Word w)=(p₀.1.val:Word w)) ∧
    (∀s root j,let pg : RootPage span (2^(Z).n):=Receiver.privatePage s root
      ;(((im).book.table pg).2.reads j).Fits w ((cat).middle (rootIndex span (2^(Z).n) pg).val)) ∧
    ∀s root,let pg : RootPage span (2^(Z).n):=Receiver.privatePage s root
      ;(2^e)*max (((im).book.table pg).2.field*((im).book.table pg).1) ((im).book.table pg).2.outputBits≤w/2 :=by
  have actual:=fromNamed_root_state (B:=B) drift degree payload e previous M nextM oldLanes primitiveLanes printedBits
    venue io floor w fitsStencil fitsSigned fitsCut count prepared degreeAt capAt measured
  have pages:=DateInputs.fromNamed_private_page_rooms (B:=B) drift degree payload e previous M nextM oldLanes
    primitiveLanes printedBits venue io floor w fitsStencil fitsSigned fitsCut count previousMeta previousArguments
    initial prepared sceneRoom degreeAt capAt ready chosen pitch small word ceiling
  have pre (j : ℕ) (earlyBound : j<(rc).origin) : (mid measured) j=measured j :=by
    rw [actual.2.2.2.2.1]
    exact ((rc).prepared_mid_window book prepared measured j (earlyBound.trans_le (rc).origin_le_projection)).trans
      (((rc).prefix_hardware prepared.toPrefixFits measured).2.2 j (.inl earlyBound))
  have geometry:=(P).S.banks (P).X (P).base (P).bank ready.stencil.operands
  have lim:=(book).limits (rc).projectionEnd HH (2^cc) (2^e)
  have rooted : (rc).origin≤ceil:=by
    rw [actual.2.2.2.1]
    exact (rc).origin_le_projection.trans (lim.1.trans (lim.2.1.trans lim.2.2))
  have earliest : (P).base≤(rc).origin:=geometry.2.2.2.2.2.2.2.2.trans ((P).S.header_before_output (P).base)
  have prior:=(ready.stencil.operands.old).levels
  have census := ready.stencil.operands.old.count
  have rawDim : (P).S.m=(E).dim:=(sh).dimension
  have wd : (E).dim=cc+k:=(sh).dimension.symm
  have admitted (v : Fin HH) (live : v.val<pop) :
      ∃u : input.V,(idx u)=v :=by
    let ord : Fin pop:=⟨v.val,live⟩
    refine ⟨(ClosedReset.Recorded.oldName input).symm ord,Fin.ext ?_⟩
    exact congrArg (fun h : Fin (Fintype.card input.V) => h.val) ((ClosedReset.Recorded.oldName input).apply_symm_apply ord)
  have physical (v : input.V) : depths (idx v)=(Z).placement.b (B.frame.host v) :=
    ClosedReset.Recorded.oldDepth_at B v
  obtain ⟨size,_,_⟩:=reservation
  have localRange (v : Fin HH) : v.val*((P).S.m+1)<(P).X.levels.size :=by
    rw [rawDim]
    have capRows : HH*((E).dim+1)≤(E).hosts := by
      rw [size]; exact Nat.mul_le_mul_left _ (by omega)
    exact ((Nat.mul_lt_mul_of_pos_right v.isLt (Nat.succ_pos _)).trans_le capRows).trans_le ready.prime.fit.hostRows.1
  have fieldBound : k+1<2^field :=by
    have depth : k+1≤field:=by
      change k+1 ≤ ResetMiddle.fieldWidth venue.degree cap n k Ht
      exact (le_max_left ..).trans (le_max_right ..)
    exact depth.trans_lt Nat.lt_two_pow_self
  have range:=ClosedReset.Window.calendar_residual B
  have heads:=stencil_header_prepared atlas sh start count io.hubs g (2^n) roots ready.stencil prepared measured order.resident
  refine ⟨actual.2.2.2.2.1.symm ▸ heads,⟨geometry.2.1.1,geometry.2.1.2.1,
    geometry.2.1.2.2.trans (((P).S.header_before_output (P).base).trans rooted)⟩,
    ⟨prior.1,prior.2.1,prior.2.2.trans (earliest.trans rooted)⟩,fun v _=>localRange v,?_,?_,?_,?_,?_,pages.1,pages.2⟩
  · intro v live;obtain ⟨u,rfl⟩:=admitted v live
    rw [physical u]
    refine (pre _ ?_).trans (panel.depth u)
    exact ((Nat.add_lt_add_left (localRange (idx u)) _).trans_le prior.2.2).trans_le earliest
  · intro v live;obtain ⟨u,rfl⟩:=admitted v live
    rw [physical u]
    have high:=(Z).placement.depth (B.frame.host u)
    have bound : (E).dim ≤ w := by omega
    have highDim := high.trans_eq (B.keyWidth.trans wd.symm)
    exact ⟨(T).commonLow _,(highDim.trans bound).trans_lt Nat.lt_two_pow_self⟩
  · intro v live;obtain ⟨u,rfl⟩:=admitted v live
    rw [physical u]
    have upper:=Nat.sub_le_sub_right ((Z).placement.depth (B.frame.host u)) coarse
    omega
  · intro q
    have baseFit : count.base<(rc).origin:=by
      have fit : count.Fits w (P).base:=census.1
      exact (Nat.lt_add_of_pos_right (Nat.two_pow_pos _)).trans_le (fit.2.2.trans earliest)
    change count.read (mid measured) (0:Word w)=_
    have read:=DescentPackedZip.bank_read count (mid measured) (i:=0) (Nat.two_pow_pos _) popFit
    calc
      _ = (mid measured) count.base := by simpa only [Nat.add_zero, Nat.cast_zero] using read
      _ = measured count.base := pre _ baseFit
      _ = _ := panel.count
  · rw [actual.2.2.2.2.1,B.commonDepth]
    exact issued_host_from_order atlas sh start count io.hubs g (2^n) roots ready.stencil rfl rfl rfl prepared measured order

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI

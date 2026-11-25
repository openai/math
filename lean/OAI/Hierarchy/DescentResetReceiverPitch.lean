import OAI.Hierarchy.DescentNamedResetOutput
import OAI.Hierarchy.DescentResetStencilPitch
import OAI.Hierarchy.DescentIssuedRootWidths

namespace OAI
/-! # A common SIMD pitch for original reset roots and the four signed endpoint families -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSixParty DescentSIMDLookup DescentPackedWalsh
open DescentResetMixedWordRAM

/-! The entries are bits in one group. A candidate's ordinal is bounded by the
relative roster. Host addresses are held in separate whole-word banks. -/
noncomputable section
variable (v : ResetOutput)

/-- The two independent GL traversals use the same public node capacity, even
at the seed where the actually stored predecessor has one node. -/
def retainedUnit : ℕ :=
  let n:=v.nodes
  let a:=v.argumentSlots
  let L:=v.sheets.blocks
  let s:=v.nodeBits
  max 1 (max (s*n) (max (s*L+s) (max ((s*L)*((2+7*a)*n)+s*L) (s*L+L*Nat.clog 2 (L+1)))))
def retainedRoleUnit : ℕ :=
  let b:=v.primitive.chart.bits
  let L:=v.sheets.blocks
  max 1 (max ((b*(2*v.nodes+1)+b)*L) (b*L+L*Nat.clog 2 (L+1)))

def rootUnits : List ℕ :=
  let m:=v.middle
  let L:=2^m.rootDepth
  let d:=v.front.donor
  let b:=d.fieldBits
  let a:=v.front.contact
  let n:=DescentFallbackPeriod.Projected.Receiver.arityLimit m.rootDegree L d.cap m.rotorBits m.rootDepth
  [DescentSixParty.PackedFlow.Padded.sharedWidth m.stencil, (m.signedBits+m.signedBits)*L,
   m.projectBits,m.stencil.n,v.rootOutputBits,m.rootField*(n+1),m.rootField*n,v.actor.unitBits,
   v.venue.census.broadcast, v.funded.precision,
   v.funded.precision*L+v.funded.precision,(v.funded.precision+v.funded.precision)*L,
   L*Nat.clog 2 (L+1),DescentSignedCableCodec.width v.venue.next.degree v.venue.next.cap,
   m.signedBits*L,v.front.projectionBits,
   DescentResetStemKey.unit m.rootDegree v.front.stemField,v.front.privateBits*(v.front.wireCap*5),
   v.front.stemField+2,v.front.peer.bits,
   b*d.boardFields+b,(b*d.laneFields)*2+b*d.laneFields,b*d.returnFields+b,b,
   d.queryBits+d.cargoBits,d.cargoBits+d.cargoBits,
   a.fieldBits*a.oldFields+a.fieldBits,a.viewBits+a.viewBits,a.fieldBits*8+a.fieldBits,
   v.front.contact.outputBits,v.sheets.metaBits,
   v.setup.packets.oldBits*(v.setup.packets.stage 0 false).fields,
   v.setup.packets.oldBits*(v.setup.packets.stage 0 true).fields]

def receiverUnits : List ℕ :=
  let a:=v.sheets
  let b:=a.metaBits
  let z:=a.zeroBits
  let C:=v.setup
  let F:=v.front
  let X:=a.blocks
  let t:=v.ticketBits
  [v.retainedUnit,v.retainedRoleUnit,v.setup.rotorBits+1,v.birth.aperture,v.birth.rootBits*X,C.publicCasts.bound,v.roleTransfer.transfer.bits*X,v.primitive.rawBits,v.primitive.chart.bits*v.primitive.chart.nodes+v.primitive.chart.bits,
   max a.selectorBits a.shortBits*(a.blocks+1),max a.stemSources.width a.metaBits,b*10,a.stemSources.width,a.selectorBits+a.shortBits,a.shortBits+a.shortBits,
   Book.unit b z a.shortBits a.shortBits,DescentOperandPairBook.unit 6 a.stemBits,a.argBits,
   Book.unit b z a.haloBits a.argBits,
   DescentResetStemKey.unit F.peer.oldDegree F.stemField,F.projectionBits*X,
   DescentResetStemMux.unit (F.stemField+2) (b*7),b*7+b,b*X,
   b*7+t,t*5+t*5,DescentResetSourceSeekRAM.keyBits 4 a.candidates+b,
   b*5+b*5,8*b+b,v.receiver.queryBits+v.receiver.valueBits,v.receiver.queryBits+v.receiver.signedBits,
   v.nodeBits*v.nodes+v.nodeBits, max v.metadata.paidBits (v.metadata.spanBits+v.metadata.chart.bits),
   C.sourceWidth,C.fieldBits,C.fieldBits*C.inputs+C.fieldBits,C.fieldBits+2,
   C.rotorBits*4+C.rotorBits,C.fallbackBits*C.fallbackInputs+C.fallbackBits,
   C.retainedFields.bits*X,C.signedFields.bits*X,
   C.packets.oldBits*(C.packets.stage 0 false).fields*X,
   C.packets.oldBits*(C.packets.stage 0 true).fields*X]

def groupWidth :=1+(v.rootUnits++v.receiverUnits).sum

theorem groupWidth_pos : 0<v.groupWidth :=Nat.add_pos_left (by decide) _

theorem groupWidth_fit {t : ℕ} (member : t∈v.rootUnits ∨ t∈v.receiverUnits) : t≤v.groupWidth :=by
  have m : t∈v.rootUnits++v.receiverUnits :=List.mem_append.mpr member
  exact (List.single_le_sum (fun _ _=>Nat.zero_le _) _ m).trans (Nat.le_add_left ..)

/-- All three independent cuts are genuine limits on the input bank used by the root,
the retained Walsh subword and the successor group array. -/
def exponent (previous transformCut nextCut h : ℕ) :=
  laneBits (min previous (min transformCut nextCut)) h v.groupWidth

theorem exponent_bounds (previous transformCut nextCut h : ℕ) :
    v.exponent previous transformCut nextCut h≤previous ∧
    v.exponent previous transformCut nextCut h≤transformCut ∧
    v.exponent previous transformCut nextCut h≤nextCut :=by
  have below : v.exponent previous transformCut nextCut h≤ min previous (min transformCut nextCut):=
    Nat.min_le_left ..
  exact ⟨below.trans (Nat.min_le_left ..),below.trans ((Nat.min_le_right ..).trans (Nat.min_le_left ..)),
    below.trans ((Nat.min_le_right ..).trans (Nat.min_le_right ..))⟩

theorem operand_room {t : ℕ} (previous transformCut nextCut h : ℕ)
    (short : 8*v.groupWidth≤h) (member : t∈v.rootUnits ∨ t∈v.receiverUnits) :
    t*2^(v.exponent previous transformCut nextCut h)≤h/2 :=by
  have full:=keys_fit (m:=min previous (min transformCut nextCut)) v.groupWidth_pos short
  have base:=Nat.mul_le_mul_right (2^(v.exponent previous transformCut nextCut h)) (v.groupWidth_fit member)
  apply base.trans
  apply le_trans _ full
  unfold bigKey
  change v.groupWidth*2^(v.exponent previous transformCut nextCut h)≤
    1+(v.groupWidth+v.groupWidth)*2^(v.exponent previous transformCut nextCut h)
  rw [Nat.add_mul]
  omega

theorem pitch_price (H previous transformCut nextCut h : ℕ) (short : 8*v.groupWidth≤h) :
    let c:=min previous (min transformCut nextCut)
    H*2^(c-v.exponent previous transformCut nextCut h)*h≤H*h+16*H*2^c*v.groupWidth :=
  per_layer H v.groupWidth_pos short
end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh ProtocolRAM
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (previous nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (addr : ℕ→ℕ→Bank) (roster : Bank)

local notation "previous₀" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "fields₀" => ResetOutput.fromBoard G S board k tail age p f g drift degree h 0 previous 1 nextM C packet previous₀ 0
local notation "d₀" => S.groupWidth k tail age+k

def receiverCut :=
  let transform:=laneBits (d₀) h (S.localWalshBits p (d₀) f (quota S.rounds))
  (fields₀).exponent previous (transform-k) (S.groupWidth k tail (age+1)) h

local notation "e₀" => receiverCut G S board k tail age p f g drift degree h previous nextM C packet oldLanes primitiveLanes printedBits venue

/-- The receiver dictionary inventory excludes address holes and sparse host IDs.
All checked receivers use the same integral power of two in the native root and next-group scans. -/
def selected (floor : ℕ) :=
  named G S board k tail age p f g drift degree h (e₀) previous (2^(e₀)) nextM C packet oldLanes primitiveLanes printedBits venue addr roster floor

local notation "issued₀" => selected G S board k tail age p f g drift degree h previous nextM C packet oldLanes primitiveLanes printedBits venue addr roster

private theorem rootsAt (e base : ℕ) :
    let v := ResetOutput.fromBoard G S board k tail age p f g drift degree h e previous (2^e)
      nextM C packet previous₀ base
    v.rootUnits = (fields₀).rootUnits := by
  dsimp only [ResetOutput.rootUnits, ResetOutput.fromBoard, ResetMiddle.fromCalendar,
    PackedFlow.Padded.sharedWidth, PackedFlow.Padded.widthUnit, DescentPlainTerminal.Suffix.StencilBook.r,
    ResetMiddle.projectBits, ActorSetup.unitBits, ActorSetup.fromCalendar,
    CandidateFront.menu, CandidateFront.setupFront, CandidateSheets.fromBoard,
    DescentNamedFundedChart.setup, DescentNamedFundedChart.shape, DescentNamedFundedChart.operandWidth,
    ResetVenue.fromBoard, ResetVenue.collect, DescentNamedFundedChart.lowCount,
    DescentContactDonorFront.Shape.boardFields, DescentContactDonorFront.Shape.laneFields,
    DescentContactDonorFront.Shape.returnFields, DescentContactPreROM.Layout.oldFields,
    DescentContactPreROM.Layout.viewBits, DescentContactPreROM.Layout.viewCount, DescentContactPreROM.Layout.half, DescentOperandRootPull.Pair.stage]

private theorem lookupFields (P Q : DescentOperandRootPull.Pair) (f : Bool)
    (deg : P.degree = Q.degree) (cap : P.cap = Q.cap) (res : P.residual = Q.residual)
    (rot : P.rotorBits = Q.rotorBits) : (P.stage 0 f).fields = (Q.stage 0 f).fields := by
  simp only [DescentOperandRootPull.Pair.stage, deg, cap, res, rot]

set_option maxHeartbeats 450000 in
private theorem receiverInventoryAt (e base : ℕ) :
    let v := ResetOutput.fromBoard G S board k tail age p f g drift degree h e previous (2^e)
      nextM C packet previous₀ base
    v.receiverUnits = (fields₀).receiverUnits := by
  intro v
  let z := fields₀
  have pack (f : Bool) := lookupFields v.setup.packets z.setup.packets f rfl rfl rfl rfl
  have lastField (b : Bool) :
      (v.setup.packets.oldBits * (v.setup.packets.stage 0 b).fields)*v.sheets.blocks =
        (z.setup.packets.oldBits * (z.setup.packets.stage 0 b).fields)*z.sheets.blocks :=
    congrArg₂ Nat.mul (congrArg₂ Nat.mul rfl (pack b)) rfl
  change v.receiverUnits = z.receiverUnits
  dsimp only [ResetOutput.receiverUnits]
  iterate 41 apply congrArg₂ List.cons rfl
  exact congrArg₂ List.cons (lastField false) (congrArg₂ List.cons (lastField true) rfl)

private theorem inventoryAt (e base : ℕ) :
    let v := ResetOutput.fromBoard G S board k tail age p f g drift degree h e previous (2^e)
      nextM C packet previous₀ base
    v.rootUnits = (fields₀).rootUnits ∧ v.receiverUnits = (fields₀).receiverUnits ∧
      v.receiver.lanes = 2^e ∧ v.middle.rootLanes = 2^e := by
  exact ⟨rootsAt G S board k tail age p f g drift degree h previous nextM C packet oldLanes primitiveLanes printedBits venue e base,
    receiverInventoryAt G S board k tail age p f g drift degree h previous nextM C packet oldLanes primitiveLanes printedBits venue e base,
    rfl, rfl⟩

theorem selected_inventory (floor : ℕ) :
    (issued₀ floor).successor.rootUnits=(fields₀).rootUnits ∧
    (issued₀ floor).successor.receiverUnits=(fields₀).receiverUnits ∧
    (issued₀ floor).successor.receiver.lanes=2^(e₀) ∧ (issued₀ floor).successor.middle.rootLanes=2^(e₀) :=
  by
    unfold selected
    rw [named_successor]
    apply inventoryAt

theorem selected_room (floor t : ℕ) (short : 8*(fields₀).groupWidth≤h)
    (live : t∈(issued₀ floor).successor.rootUnits ∨ t∈(issued₀ floor).successor.receiverUnits) :
    t*(issued₀ floor).successor.receiver.lanes≤h/2 :=
  by
    obtain ⟨roots, receivers, lanes, _⟩ := selected_inventory G S board k tail age p f g drift degree h previous nextM C packet oldLanes primitiveLanes printedBits venue addr roster floor
    rw [roots, receivers] at live
    rw [lanes]
    exact (fields₀).operand_room previous
      (laneBits (d₀) h (S.localWalshBits p (d₀) f (quota S.rounds))-k)
      (S.groupWidth k tail (age+1)) h short live

theorem selected_cut :
    e₀≤previous ∧ e₀≤laneBits (d₀) h (S.localWalshBits p (d₀) f (quota S.rounds))-k ∧
    e₀≤S.groupWidth k tail (age+1) :=(fields₀).exponent_bounds ..
end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI

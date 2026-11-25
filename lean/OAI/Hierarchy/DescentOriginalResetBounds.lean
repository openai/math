import OAI.Hierarchy.DescentOriginalOperandSetup
import OAI.Hierarchy.DescentOriginalPublishedRegisters
import OAI.Hierarchy.DescentOriginalMiddleRegions
import OAI.Hierarchy.DescentOriginalFundedSetup
import OAI.Hierarchy.DescentNamedResetVenueRate
import OAI.Hierarchy.DescentDatedResetScalarRoom

namespace OAI
/-! # Bounding a whole compiled reset from its dated public parameters and two predecessor words -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty Filter
noncomputable section
variable {F : Type} [Field F] (G:PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
variable (op : RotorSpec) (t f g reset τ D drift B : ℕ) {ι : ℕ→Type*}
variable (sites age size degree root previous nextM base : ∀h,ι h→ℕ) (old : ∀h,ι h→Prior)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg i:arg => stageNumbers G t (J_ h) f g reset (sites h i) (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "a_" h:arg i:arg => originalSample G op t f g reset τ D drift (J_ h) (sites h i) (age h i)
  (size h i) (degree h i) h (root h i) (previous h i) (2^(root h i)) (nextM h i) (base h i) (old h i)
set_option quotPrecheck false in
local notation "out_" => fun h i=>(a_ h i).output G board D f g op.C op.w

open DescentSixParty.PackedFlow.Canvas DescentPackedFlowPublication
set_option quotPrecheck false in
local notation "c_" h:arg i:arg => (S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i)

/-- The independent estimator prefix uses the physically issued input banks at its true floor. -/
structure EntranceRoom (a : ∀h,ι h→PhysicalReset) (floor : ∀h,ι h→ℕ) : Prop where
  canvas : Placement.ScalarRoom (fun h i=>(a h i).chart ((a h i).stageStart (floor h i))) (fun h i=>(a h i).payload) (fun h i=>(a h i).gain)
  radix : Bounded (fun h i=>2^(a h i).k)
  axes : Bounded (fun h i=>2^((a h i).high+(a h i).low))
  book : ∀ᶠ h:ℕ in atTop,∀i,let v:=a h i;Book.width v.bits (2^v.k) v.short*v.lanes≤v.payload
  groups : Bounded (fun h i=>(a h i).groups)
  lanes : Bounded (fun h i=>2^(a h i).e)
  reblock : ∀ᶠ h:ℕ in atTop,∀i,let v:=a h i;v.re+v.field*(2^v.re*2^v.e)≤v.payload/2

theorem original_reset_bounds (a : ∀h,ι h→PhysicalReset) (floor : ∀h,ι h→ℕ)
    (date : ∀h i,(a h i).successor=out_ h i) (payload : ∀h i,(a h i).payload=h)
    (entry : EntranceRoom a floor) (positive : 0<B) (branch : G.b≤2^(capRate G t g)) (bound : ℕ)
    (short : ∀h i,size h i≤h) (degrees : ∀h i,degree h i≤bound)
    (seed : Bounded sites) (before : ∀h i,age h i<(S_ h i).length)
    (cuts : ∀h i,root h i≤previous h i ∧ previous h i≤c_ h i)
    (next : ∀h i,root h i≤(S_ h i).groupWidth (k_ h) (tail τ (J_ h)) (age h i+1))
    (host : ∀h i,(old h i).venue.hosts=(S_ h i).hostSize (age h i))
    (group : ∀h i,(old h i).venue.groups=(S_ h i).groupCount (age h i))
    (block : ∀h i,(old h i).venue.k=k_ h)
    (nextMask : ∃K:ℕ,∀ᶠ h:ℕ in atTop,∀i,nextM h i≤K*h)
    (previousKey : ∀ᶠ h:ℕ in atTop,∀i,(out_ h i).middle.signedBits*2^(previous h i)≤h/2)
    (paid : ∀ᶠ h:ℕ in atTop,∀i,(S_ h i).censusBits (size h i)*(old h i).venue.lanes≤h/2 ∧
      (old h i).venue.lanes≤h)
    (caps : ∀ᶠ h:ℕ in atTop,∀i,(old h i).nodes≤(S_ h i).retainedNodes ∧
      (old h i).arguments≤(S_ h i).retainedArgumentsAt G drift)
    (operandLanes : Bounded (fun h i=>(old h i).operandLanes))
    (roleLanes : Bounded (fun h i=>(old h i).primitiveLanes))
    (archive : ∀ᶠ h:ℕ in atTop,∀i,let v:=out_ h i;
      v.setup.retained.wholeWord*(old h i).operandLanes≤h/2 ∧ v.roleTransfer.transfer.wholeWord*(old h i).primitiveLanes≤h/2)
    (selected : ∀ᶠ h:ℕ in atTop,∀i,8*(out_ h i).groupWidth≤h) (priced : Installed (out_)) :
    PhysicalReset.ScalarRoom a (fun h i=>(a h i).stageStart (floor h i)) :=by
  let p:=out_
  have inside:=fun h i=>(before h i).le
  have cal:=original_inputs G board op t f g reset τ D drift B sites age size degree root previous nextM base old
    positive branch bound short degrees
  have level : ∀ᶠ h:ℕ in atTop,J_ h≤h:=Eventually.of_forall fun h=>(Nat.div_le_self ..).trans (Nat.log_le_self 2 h)
  have m:=original_middle G board op t f g reset τ D drift B sites age size degree root previous nextM base old
    positive branch bound short degrees seed inside cuts next previousKey priced
  obtain ⟨front,contacts,private_,sheets,actor⟩:=original_region_rooms G board op t f g reset τ D drift B sites age size degree root previous nextM base old
    positive branch bound short degrees seed inside next priced
  have saved:=original_published G board op t f g reset τ D drift B sites age size degree root previous nextM base old
    positive branch bound short degrees seed inside next priced
  obtain ⟨setup,role⟩:=original_operand_setup G board op t f g reset τ D drift B sites age size degree root previous nextM base old
    positive branch bound short degrees seed before next caps operandLanes roleLanes archive selected priced
  have fund:=original_funded_room G board op t f g reset τ D drift B sites age size degree root previous nextM base old
    seed inside (fun h i=>(cuts h i).1.trans (cuts h i).2) host group block paid priced
  have venue:=original_venue_room G board op t f g reset τ D drift B sites age size degree root previous nextM base old
    positive branch bound short degrees seed inside host block next priced nextMask
  have nodeKey : ∀ᶠ h:ℕ in atTop,∀i,let v:=p h i;(v.nodeBits*v.nodes+v.nodeBits)*v.receiver.lanes≤h := by
    filter_upwards [priced] with h keys
    intro i
    let v := p h i
    have key : v.nodeBits * v.nodes + v.nodeBits ∈ v.receiverUnits := by simp [receiverUnits]
    exact (keys i _ (.inr key)).trans (Nat.div_le_self ..)
  constructor
  case canvas => exact entry.canvas
  case radix => exact entry.radix
  case axes => exact entry.axes
  case initialBook => exact entry.book
  case groups => exact entry.groups
  case lanes => exact entry.lanes
  case reblock => exact entry.reblock
  all_goals simp only [date]
  case setup => exact setup
  case actor => exact actor
  case jointDigits => exact saved.jointDigits
  case privateViews => exact private_
  case contactOutput => exact contacts
  case candidatesFront => exact front
  case candidatesSheets => exact sheets
  case weighted => exact m.stencil
  case oldBlocks => exact m.blocks
  case signedLanes => exact m.lanes
  case signedRatio => exact m.ratio
  case signedPorts => exact m.ports
  case signedHosts => exact m.hosts
  case signedDimension => exact m.dimension
  case signedHigh => exact m.high
  case signedWord => simp only [payload]; exact m.word
  case signedMatrix => simp only [payload]; exact m.matrix
  case rootGroups => exact m.rootGroups
  case rootShapes => exact m.shapes
  case rootField => exact m.field
  case rootLawWidth => exact m.law
  case blocks => exact sheets.blocks
  case capacity => exact saved.cap
  case packedLanes => exact sheets.lanes
  case receiverHosts => exact sheets.hosts
  case receiverGroups => exact sheets.groups
  case candidates => exact sheets.candidates
  case «fields» => exact saved.fields
  case argumentSlots => exact saved.arguments
  case transfer => exact role
  case birth => exact saved.birth
  case primitive => exact saved.primitive
  case metadata => exact saved.metadata
  case funded => exact fund
  case venue => exact venue
  case rotorBins => exact Bounded.const (ι:=ι) (2^n)
  case degrees => exact Bounded.const (ι:=ι) D
  case nodes => exact cal.nodes.bounded level
  case controlDigits =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact saved.controlDigits
  case rankKey =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact saved.rankKey
  case nodeKey =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact nodeKey
  case keepDigits =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact saved.keepDigits
  case dictionaries =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact saved.dictionaries
  case retileKey =>
    refine ⟨1, ?_⟩
    simp only [Nat.one_mul]
    exact m.retile.mono fun h word i => (word i).trans (Nat.div_le_self ..)
  case rootHosts => exact m.hosts
  case rootLanes => exact sheets.lanes
  case rootBlocks => exact sheets.blocks

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI

import OAI.Hierarchy.DescentDatedOrdinaryRangeExit
import OAI.Hierarchy.DescentOrdinaryIssuedRange
import OAI.Hierarchy.DescentArchiveOriginalSlot
import OAI.Hierarchy.DescentOriginalRangeSlots

namespace OAI
/-! # Reading the semantic operand interval after both ordinary counters have run -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentCompiler DescentSIMDLookup
open DescentColonies DescentDatedPriorOperand DescentRetainedRangeDigits DescentLocalArchiveOrder
open DescentKernelHistory Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
set_option maxRecDepth 8192
set_option maxHeartbeats 800000
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (root shelf header : ℕ)
  (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
  {w : ℕ} (s : PhysicalOrdinary.ResultSteps w) (bank : v.ResultRoom (v.stageStart root) B w)
  (d : DonorDate) (positive : 0<d.exponent) (fit : PhysicalOrdinary.Room v root shelf header input count wires s d)
local notation "floor" => v.stageStart root
local notation "meter" => d.counter v.payload ((d.schedule v.payload v.seats v.bitsPerField).rotationEnd input.roster floor) header
local notation "op" => v.argumentsAfter floor bank.operands
  (by rw [v.after_end floor bank.geometry]; exact bank.limit)
local notation "code" => v.date root shelf header input count wires B s bank d positive


open DescentPackedColony DescentOrdinaryAtomFieldRAM.ScalarOperand DescentPackedOperand DescentOperandStateBanks
open DescentSIMDLookup DescentBundleHistory
variable (dates : ℕ→DateCode w) (initial : Memory w) (i : ℕ) (issued : dates i=(v.date root shelf header input count wires B s bank d positive))
local notation "work" => v.beforeArgumentWrite root shelf header input count wires B s d positive fit (DateCode.history dates initial i)
local notation "target" => DateCode.history dates initial (i+1)
local notation "ports" => ordinary v floor
variable (blocks : 2^v.venue.k=v.resolver.blocks) (groups : v.venue.groups=v.resolver.groups)
  (saved : ((d.counter v.payload ((d.schedule v.payload v.seats v.bitsPerField).rotationEnd input.roster (v.stageStart root)) header)).endAddr≤v.finalChart.out (v.metaEnd (v.stageStart root))) (away : header<((d.counter v.payload ((d.schedule v.payload v.seats v.bitsPerField).rotationEnd input.roster (v.stageStart root)) header)).endAddr)
local notation "layoutEq" => ordinary_range_layout v floor blocks groups
variable {k wire hist z D dim p R : ℕ} {bits : P→ℕ} {W : MarkedWorld F dim P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} (r : Reached W G q ε S k (i+1) z D wire hist)
  (bitsAt : BitDescription W) (order : Local bitsAt) (places : RangeRoom (ordinary v (v.stageStart root)) r bitsAt)
  (shape : WorldShape p R bitsAt)
local notation "coord" x:arg => Reached.NodeCells.coordinate r (x:NodeOrder.All bitsAt).1
local notation "bx" x:arg => (coord x).2.2.cast (congrArg (2^·) places.radix)
local notation "gx" x:arg => (coord x).2.1.cast places.groups
local notation "hx" x:arg => (⟨(coord x).1.val,places.hosts (x).1⟩ : Fin (ports).operandHosts)
local notation "nx" x:arg => (order (x).1 (x).2).castLE (places.capacity (x).1)
local notation "keyAt" j:arg f:arg => DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j

include issued saved away in
theorem ordinary_archived_range_values
    («meta»:v.MetaWords) (old:Books v.resolver) (jobs:Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver)
    (metadata:∀f x,Reads (v.nodeChart.bank (v.nodeBankBase floor) f x) («meta» f x) v.resolver.lanes work)
    (spans:∀x pg,Reads (previousBank v.resolver (v.vectorOutput floor) x pg) (old x pg) v.resolver.lanes work)
    (keys:∀a,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) a)
      (fun h g=>word ((jobs a).compiled h g)) v.resolver.lanes work)
    (width:v.finalChart.field*v.resolver.nodes*v.resolver.lanes≤w)
    (original:∀x n h g (j:Fin v.resolver.operands) (f:Fin 3),let owner:=slotAt ports r bitsAt order places x n h g
      owner.elim True (fun y=>j.val<(occurrences (shape.sites y.1) y.2).length ∨ f=2) →
      (take n (old (x.cast blocks) (keyAt (j:Fin v.resolver.operands) f) h (g.cast groups))).val=
        owner.elim 0 (fun y=>atSlot (shape.sites y.1) y.2 j.val f))
    (y:NodeOrder.All bitsAt) (j:Fin (ports).argumentsPerNode) (f:Fin 3)
    (need:j.val<(occurrences (shape.sites y.1) y.2).length ∨ f=2) :
    (rangeRegister ports r bitsAt order places.capacity places.hosts places.groups places.radix places.positive target).word y j.val f=
      atSlot (shape.sites y.1) y.2 j.val f:=by
  have kept:=rangeRegister_at_ordinary v root shelf header input count wires B s bank d positive fit dates initial i
    ports issued rfl blocks groups saved away r bitsAt order places.capacity places.hosts places.groups places.radix places.positive
  rw [kept]
  have read:=v.issued_range_at floor bank.operands (by rw [v.after_end floor bank.geometry];exact bank.limit)
    work «meta» old jobs metadata spans keys
    (fun x:NodeOrder.All bitsAt=>(bx x).cast (congrArg Layout.blocks layoutEq))
    (fun x:NodeOrder.All bitsAt=>(hx x).cast (congrArg Layout.hosts layoutEq))
    (fun x:NodeOrder.All bitsAt=>(gx x).cast (congrArg Layout.groups layoutEq))
    (fun x:NodeOrder.All bitsAt=>(nx x).cast (congrArg Layout.nodes layoutEq)) places.positive width y j f
  have found:=slotAt_original ports r bitsAt order places y.1 y.2
  have meaning:=original (bx y) (nx y) (hx y) (gx y) j f
  dsimp only at meaning
  rw [found] at meaning
  exact read.trans (meaning need)

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI

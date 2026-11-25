import OAI.Hierarchy.DescentDatedOrdinaryArgumentExit
import OAI.Hierarchy.DescentRangeRegisterFrame
import OAI.Hierarchy.DescentDatedRangeRegisters
import OAI.Hierarchy.DescentPhysicalDateHistory

namespace OAI
/-! The registered range at a real ordinary date reads the operand scan before its two counters. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentPacking.PackedMatch.Local.Stage DescentCompiler DescentSIMDLookup
open DescentColonies DescentDatedPriorOperand DescentRetainedRangeDigits DescentLocalArchiveOrder
open DescentKernelHistory Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] (v : PhysicalOrdinary F P) (root shelf header : ℕ)
  (input : Dated.Operands) (count : Bank) (wires : v.signed.Input) (B : StageVenueTail.Sources)
  {w : ℕ} (s : PhysicalOrdinary.ResultSteps w) (bank : v.ResultRoom (v.stageStart root) B w)
  (d : DonorDate) (positive : 0<d.exponent) (fit : PhysicalOrdinary.Room v root shelf header input count wires s d)
local notation "floor" => v.stageStart root
local notation "meter" => d.counter v.payload ((d.schedule v.payload v.seats v.bitsPerField).rotationEnd input.roster floor) header
local notation "op" => v.argumentsAfter floor bank.operands
  (by rw [v.after_end floor bank.geometry]; exact bank.limit)
local notation "code" => v.date root shelf header input count wires B s bank d positive

theorem ordinary_range_layout (base : ℕ) (blocks : 2^v.venue.k=v.resolver.blocks)
    (groups : v.venue.groups=v.resolver.groups) : (ordinary v base).rangeLayout=v.resolver := by
  change (⟨2^v.venue.k,v.resolver.nodes,v.resolver.operands,v.resolver.hosts,v.venue.groups,
    v.resolver.lanes,v.resolver.size+2-2⟩ : Layout)=v.resolver
  rw [blocks,groups,Nat.add_sub_cancel]

variable (dates : ℕ→DateCode w) (initial : Memory w) (i : ℕ)
local notation "snap" => DateCode.history dates initial i
local notation "target" => DateCode.history dates initial (i+1)
local notation "written" => (op).image (v.beforeArgumentWrite root shelf header input count wires B s d positive fit snap)
variable (ports : DatePorts) (issued : dates i=v.date root shelf header input count wires B s bank d positive)
    (returned : ports=ordinary v (v.stageStart root))
  (blocks : 2^v.venue.k=v.resolver.blocks) (groups : v.venue.groups=v.resolver.groups)
  (saved : (d.counter v.payload ((d.schedule v.payload v.seats v.bitsPerField).rotationEnd input.roster (v.stageStart root)) header).endAddr≤v.finalChart.out (v.metaEnd (v.stageStart root)))
  (away : header<(d.counter v.payload ((d.schedule v.payload v.seats v.bitsPerField).rotationEnd input.roster (v.stageStart root)) header).endAddr)
local notation "layoutEq" => (congrArg rangeLayout returned).trans (ordinary_range_layout v floor blocks groups)

variable {k wiresN histN z D m : ℕ} {bits : P→ℕ} {W : MarkedWorld F m P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} (r : Reached W G q ε S k (i+1) z D wiresN histN)
  (bitsAt : BitDescription W) (order : ∀y,(bitsAt.recipe y).Node≃Fin (Fintype.card (bitsAt.recipe y).Node))
  (capacity : ∀y,Fintype.card (bitsAt.recipe y).Node≤ports.nodes)
  (hosts : ∀y,(Reached.NodeCells.coordinate r y).1.val<ports.operandHosts)
  (groupAt : S.groupCount (i+1)=ports.venue.groups) (radix : k=ports.venue.k) (pos : 0<ports.operandLanes)

local notation "coords" x => Reached.NodeCells.coordinate r (x).1
local notation "l" => ports.rangeLayout

include issued saved away in
theorem rangeRegister_at_ordinary :
    let eqLayout : ports.rangeLayout=v.resolver := layoutEq
    rangeRegister ports r bitsAt order capacity hosts groupAt radix pos target=
      fromRAM (PriorResetArchive.ordinary v floor) v.resolver v.finalChart.field written
        (by rw [←congrArg Layout.lanes eqLayout]; exact (show 0<ports.rangeLayout.lanes from pos))
        (fun x : NodeOrder.All bitsAt=>((coords x).2.2.cast (congrArg (2^·) radix)).cast (congrArg Layout.blocks eqLayout))
        (fun x : NodeOrder.All bitsAt=>(⟨(coords x).1.val,hosts x.1⟩:Fin (l).hosts).cast (congrArg Layout.hosts eqLayout))
        (fun x : NodeOrder.All bitsAt=>((coords x).2.1.cast groupAt).cast (congrArg Layout.groups eqLayout))
        (fun x : NodeOrder.All bitsAt=>((order x.1 x.2).castLE (capacity x.1) : Fin (l).nodes).cast (congrArg Layout.nodes eqLayout)) := by
  intro eqLayout
  have arch : ports.archive=PriorResetArchive.ordinary v floor := by rw [returned]; rfl
  have width : ports.operandBits=v.finalChart.field := by rw [returned]; rfl
  unfold rangeRegister
  rw [arch,width]
  apply fromRAM_layout_frame _ _ _ eqLayout
  intro x p t
  let address := (previousBank v.resolver (v.finalChart.out (v.metaEnd floor)) x p).base+t.val
  apply DateCode.history_event dates initial i (Q:=fun out=>out address=written address)
  refine ⟨v.dateOutput root shelf header input count wires B s bank d positive fit snap,?_,?_⟩
  · rw [issued]
    exact (v.date_any root shelf header input count wires B s bank d positive fit snap).1
  · exact v.date_argument_word root shelf header input count wires B s bank d positive fit snap x p t saved away

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI

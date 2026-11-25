import OAI.Hierarchy.DescentResetArchiveCertificate
import OAI.Hierarchy.DescentResetReachedNodeMetadata
import OAI.Hierarchy.DescentPostedOrdinalSpanSource

namespace OAI
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentPacking.PackedMatch.Local.Stage DescentColonies
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedColony DescentPackedZip
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentPrimitivePalette RegisterTimeline
open DescentDatedNodeMetadata DescentOperandStateBanks DescentOperandCandidateLookup DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} {floor w : ℕ} (u : a.DateInputs floor w)
local notation "v" => a.successor
local notation "b" => a.rebased floor
local notation "A" => (v).receiver
local notation "s" => u.operand
local notation "start" => (v).sheetsStart b
local notation "plan" => (v).linkedRankInputs u.sectors start
local notation "rendered" => (v).renderFromRanks plan b
local notation "ports" => reset a floor u
local notation "head" => a.throughPublishedRoots u.shape floor u.count u.hub u.g u.Y u.roots u.book u.src u.sourceRows u.oldDegree w u.bookFits
local notation "ht" => a.throughPublishedTicks u.shape floor u.count u.hub u.g u.Y u.roots u.book u.sourceRows u.oldDegree w u.bookFits
local notation:max "acted" m:arg actorMem:arg => ((head).seq ((v).actor.actorBody u.actor ((v).middle.stop b) w)).Exec m actorMem
  (ht+(v).actor.actorTicks u.actor ((v).middle.stop b) w)



variable {F P:Type} [Field F] [Fintype P] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:DescentCompiler.AtomSchedule} {k age grain degree wire hist p R seedGrain:ℕ}
  (r:Reached W G q ε S k age grain degree wire hist) (B:BitDescription W) (number:Local B)
  (places:RangeRoom (reset a floor u) r B) (shape:WorldShape p R B) (hp:0<p) (pin:P→ℕ)
  (op:RotorSpec) (label:NodeOrder.All B→Label G hist seedGrain op)
local notation "L" => (ports).rangeLayout
local notation "R₁" => (v).rangeLayout
local notation "c₀" => (ports).metadataChart
local notation "c₁" => (v).metadata.chart
local notation "slot" => slotAt ports r B number places
local notation "flags" => archiveFlag r B number ports places
local notation "ptr" => Reached.argumentPointer r B number shape hp pin (ports).argumentsPerNode
local notation:max "argc" y:arg => (DescentRetainedRangeDigits.occurrences (shape.sites (y:NodeOrder.All B).1) y.2).length
local notation:max "reg" m:arg => rangeRegister ports r B number places.capacity places.hosts places.groups places.radix places.positive m

private theorem move_span_read {H H' G G' M M' width width' w : ℕ} (hosts : H=H') (groups : G=G')
    (pitch : M=M') (bits : width=width') (expr : Expr) (mem : Memory w)
    (cells : Fin H→Fin G→Cell width) (read : Source expr cells M mem) :
    Source expr (fun h g=>(cells (h.cast hosts.symm) (g.cast groups.symm)).cast (congrArg (2^·) bits)) M' mem:=by
  subst H';subst G';subst M';subst width'
  exact read

omit [Fintype P] in
/-- The current physical span words are determined by the issued operands and their blank
rows before any primitive-role register is read. -/
theorem acquired_span_register (z:u.FinalInputs) (ok:u.Ready) (room:z.Room) {m mid:Memory w}
    (before:u.throughOperandDate.Runs m mid)
    (small:2*(A).candidates<2^(A).queryBits) (axes:L=R₁) (chart:c₀=c₁)
    (actorMem : Memory w) (issued : acted m actorMem)
    (choice : ∀i,OrdinalRead u ok small actorMem i)
    (spanFields : ∀(x:Fin (L).blocks)(j:Fin (L).operands)(f:Fin 3) h g n y,slot x n h g=some y → (j.val<argc y ∨ f=2) →
        ((choice ((v).operandOrdinal (s) (DescentRetainedRangeDigits.page f) ((j.cast (congrArg Layout.operands axes)).cast ok.slots.symm)
          (x.cast (congrArg Layout.blocks axes)) ((n.cast (congrArg Layout.nodes axes)).cast ok.nodes.symm))).amount
          (h.cast (congrArg Layout.hosts axes)) (g.cast (congrArg Layout.groups axes))).val=DescentRetainedRangeDigits.atSlot (shape.sites y.1) y.2 j.val f)
    (emptySpan : ∀(x:Fin (L).blocks)(j:Fin (L).operands) h g n,slot x n h g=none →
      ((choice ((v).operandOrdinal (s) 6 ((j.cast (congrArg Layout.operands axes)).cast ok.slots.symm)
        (x.cast (congrArg Layout.blocks axes)) ((n.cast (congrArg Layout.nodes axes)).cast ok.nodes.symm))).amount
        (h.cast (congrArg Layout.hosts axes)) (g.cast (congrArg Layout.groups axes))).val=0)
    (live : 0<(A).lanes) (signedRoom : (A).signedBits*(A).lanes≤w)
    (hostAxis : (A).hosts=(c₁).hosts) (groupAxis : (A).groups=(c₁).groups)
    (laneAxis : (A).lanes=(c₁).lanes) (spanAxis : (s).coeff=(v).metadata.spanBits)
    :
    ∃ sp : Fin (c₁).blocks→Fin (c₁).nodes→Fin (s).slots→Fin (c₁).hosts→Fin (c₁).groups→Cell (v).metadata.spanBits,
      (∀x n j,Source (z.spans x n j) (sp x n j) (c₁).lanes (z.venueImage mid)) ∧
      ∀x n j h g,(sp x n j h g).val=
        (slot (x.cast (congrArg Chart.blocks chart).symm) (n.cast (congrArg Chart.nodes chart).symm)
          (h.cast (congrArg Chart.hosts chart).symm) (g.cast (congrArg Chart.groups chart).symm)).elim 0
          (fun y=>DescentRetainedRangeDigits.atSlot (shape.sites y.1) y.2 j.val 2) :=by
  let addr (x : Fin (c₁).blocks) (n : Fin (c₁).nodes) (j : Fin (s).slots) :=
    (v).operandOrdinal (s) 6 j (x.cast z.metaBlocks) (n.cast z.metaNodes)
  let values (x : Fin (c₁).blocks) (n : Fin (c₁).nodes) (j : Fin (s).slots) (h : Fin (c₁).hosts) (g : Fin (c₁).groups) :=
    ((choice (addr x n j)).amount (h.cast hostAxis.symm) (g.cast groupAxis.symm)).cast (congrArg (2^·) spanAxis)
  have raw:=venue_ordinal_spans u ok small actorMem z room before issued choice live signedRoom
  have seen x n j : Source (z.spans x n j) (values x n j) (c₁).lanes (z.venueImage mid):=
    move_span_read hostAxis groupAxis laneAxis spanAxis _ _ _ (raw x n j)
  have counts (x : Fin (c₁).blocks) (n : Fin (c₁).nodes) (j : Fin (s).slots)
      (h : Fin (c₁).hosts) (g : Fin (c₁).groups) :
      (values x n j h g).val=(slot (x.cast (congrArg Chart.blocks chart).symm)
        (n.cast (congrArg Chart.nodes chart).symm) (h.cast (congrArg Chart.hosts chart).symm)
        (g.cast (congrArg Chart.groups chart).symm)).elim 0
          (fun y=>DescentRetainedRangeDigits.atSlot (shape.sites y.1) y.2 j.val 2):=by
    let X:=x.cast (congrArg Chart.blocks chart).symm
    let N:=n.cast (congrArg Chart.nodes chart).symm
    let H:=h.cast (congrArg Chart.hosts chart).symm
    let V:=g.cast (congrArg Chart.groups chart).symm
    let J:=j.cast (ok.slots.trans (congrArg Layout.operands axes).symm)
    change _=(slot X N H V).elim 0 _
    cases atCell : slot X N H V with
    | none=>exact emptySpan X J H V N atCell
    | some y=>exact spanFields X J 2 H V N y atCell (Or.inr rfl)
  exact ⟨values,seen,counts⟩

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI

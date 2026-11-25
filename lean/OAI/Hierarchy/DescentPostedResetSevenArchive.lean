import OAI.Hierarchy.DescentRegisteredResetArchive

namespace OAI
/-! # The genuine reset return archive -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
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

omit [Fintype P] in
/-- The one published actor image supplies all seven input digits. In particular the three
interval digits can be checked before the final operand/metadata/role return. -/
theorem reset_from_posted_seven (z:u.FinalInputs) (ok:u.Ready) (room:z.Room) {m mid out:Memory w}
    (before:u.throughOperandDate.Runs m mid) (ran:(PhysicalReset.date z).Runs m out)
    (coeff:(s).coeff=(v).nodeBits) (small:2*(A).candidates<2^(A).queryBits) (axes:L=R₁) (chart:c₀=c₁)
    (actorMem : Memory w) (issued : acted m actorMem)
    (choice : ∀i,OrdinalRead u ok small actorMem i)
    (headers : ∀(x:Fin (L).blocks)(j:Fin (L).operands)(f:Fin 4) h g n y,slot x n h g=some y → j.val<argc y →
        ((choice ((v).operandOrdinal (s) (f.castLE (by decide:4≤7)) ((j.cast (congrArg Layout.operands axes)).cast ok.slots.symm)
          (x.cast (congrArg Layout.blocks axes)) ((n.cast (congrArg Layout.nodes axes)).cast ok.nodes.symm))).amount
          (h.cast (congrArg Layout.hosts axes)) (g.cast (congrArg Layout.groups axes))).val=(ptr y j.val).header f)
    (spanFields : ∀(x:Fin (L).blocks)(j:Fin (L).operands)(f:Fin 3) h g n y,slot x n h g=some y → (j.val<argc y ∨ f=2) →
        ((choice ((v).operandOrdinal (s) (DescentRetainedRangeDigits.page f) ((j.cast (congrArg Layout.operands axes)).cast ok.slots.symm)
          (x.cast (congrArg Layout.blocks axes)) ((n.cast (congrArg Layout.nodes axes)).cast ok.nodes.symm))).amount
          (h.cast (congrArg Layout.hosts axes)) (g.cast (congrArg Layout.groups axes))).val=DescentRetainedRangeDigits.atSlot (shape.sites y.1) y.2 j.val f)
    (amount:Fin (c₁).blocks→Fin (c₁).hosts→Fin (c₁).groups→Cell (v).metadata.paidBits)
    (sp:Fin (c₁).blocks→Fin (c₁).nodes→Fin (s).slots→Fin (c₁).hosts→Fin (c₁).groups→Cell (v).metadata.spanBits)
    (arity:Fin (c₁).blocks→Fin (c₁).nodes→Fin (c₁).hosts→Fin (c₁).groups→ℕ)
    (bounded:∀x n h g,arity x n h g≤(s).slots)
    (live:∀x n j h g,sp x n j h g≠0 ↔ j.val<arity x n h g)
    (counts:∀x,Source ((PhysicalReset.FinalInputs.paid u) x) (amount x) (c₁).lanes (z.tokenImage (z.roleInput mid)))
    (ranges:∀x n j,Source (z.spans x n j) (sp x n j) (c₁).lanes (z.tokenImage (z.roleInput mid)))

    (countAt:∀x n h g,let X:=x.cast (congrArg Chart.blocks chart);let N:=n.cast (congrArg Chart.nodes chart)
      let H:=h.cast (congrArg Chart.hosts chart);let J:=g.cast (congrArg Chart.groups chart)
      (if N.val<(amount X H J).val then 1 else 0)=flags x n h g)
    (arityAt:∀x n h g,arity (x.cast (congrArg Chart.blocks chart)) (n.cast (congrArg Chart.nodes chart))
      (h.cast (congrArg Chart.hosts chart)) (g.cast (congrArg Chart.groups chart))=(slot x n h g).elim 0 (fun y=>argc y))
    (roles:∀x:Fin (2^(ports).venue.k),Reads ((ports).archive.roles.bank x.val) (fun h g=>
      encode (printedBits G hist seedGrain op) (ports).nodes (fun n=>(slot x n h g).elim 0
        (fun y=>token G hist seedGrain op (label y)))) (ports).roleLanes out):
    ArchiveRead ports r B number places shape op label ptr flags out:=by
  obtain ⟨reached,other,output⟩:=reset_archive_values u z ok room before ran coeff small axes
  have same : reached=actorMem:=ProtocolRAM.exec_unique _ m reached actorMem other issued
  subst reached
  refine ⟨?_,?_,?_,?_,roles⟩
  · intro x j f
    obtain ⟨cells,seen,fromOld⟩:=output choice x j (f.castLE (by decide:4≤7))
    exact ⟨cells,seen,fun h g n y hit real=>(fromOld h g n).trans (headers x j f h g n y hit real)⟩
  · intro x j f
    obtain ⟨cells,seen,fromOld⟩:=output choice x j (DescentRetainedRangeDigits.page f)
    exact ⟨cells,seen,fun h g n y hit real=>(fromOld h g n).trans (spanFields x j f h g n y hit real)⟩
  · intro x
    exact reset_archive_metadata u z room ran before chart amount sp arity bounded live counts ranges 0 flags
      (fun x n h g=>by simpa using countAt x n h g) x
  · intro x
    have rows : (fun (h : Fin (ports).operandHosts) (g : Fin (ports).venue.groups) =>
        encode (ports).operandBits (ports).nodes (fun n => (slot x n h g).elim 0
          (fun y => (argc y : Cell (ports).operandBits)))) =
        (fun h g => encode (ports).operandBits (ports).nodes (fun n =>
          (((slot x n h g).elim 0 (fun y => argc y) : ℕ) : Cell (ports).operandBits))) := by
      funext h g
      apply congrArg (encode (ports).operandBits (ports).nodes)
      funext n
      cases slot x n h g <;> rfl
    rw [rows]
    exact reset_archive_metadata u z room ran before chart amount sp arity bounded live counts ranges 1
      (fun x n h g=>(slot x n h g).elim 0 (fun y=>argc y))
      (fun x n h g=>by simpa using arityAt x n h g) x

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI

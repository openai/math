import OAI.Hierarchy.DescentResetArchiveCertificate

namespace OAI
/-! The retained and newly introduced operand headers share the same posted ordinal registers. -/
namespace Hierarchy.DescentSixParty.Chronology.DatePorts
open DescentDatedAddressBook DescentDatedPriorOperand DescentPackedColony DescentPackedZip
open DescentKernelHistory DescentLocalArchiveOrder DescentBundleHistory DescentPrimitivePalette RegisterTimeline
open DescentColonies DescentDatedNodeMetadata DescentOperandStateBanks DescentOperandCandidateLookup DescentSIMDLookup Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
open DescentPacking.PackedMatch.Local.Stage
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
local notation "acted" m:arg actorMem:arg => ((head).seq ((v).actor.actorBody u.actor ((v).middle.stop b) w)).Exec m actorMem
  (ht+(v).actor.actorTicks u.actor ((v).middle.stop b) w)



variable {F P:Type} [Field F] [Fintype P] {d:ℕ} {bits:P→ℕ} {W:MarkedWorld F d P bits} {G:PoweredGadget F}
  {q ε:ℝ} {S:DescentCompiler.AtomSchedule} {k age grain degree wire hist p R seedGrain:ℕ}
  (r:Reached W G q ε S k age grain degree wire hist) (B:BitDescription W) (number:Local B)
  (places:RangeRoom ports r B) (shape:WorldShape p R B) (hp:0<p) (pin:P→ℕ)
  (op:RotorSpec) (label:NodeOrder.All B→Label G hist seedGrain op)
local notation "L" => (ports).rangeLayout
local notation "R₁" => (v).rangeLayout
local notation "c₀" => (ports).metadataChart
local notation "c₁" => (v).metadata.chart
local notation "slot" => slotAt ports r B number places
local notation "flags" => archiveFlag r B number ports places
local notation "ptr" => Reached.argumentPointer r B number shape hp pin (ports).argumentsPerNode
local notation "argc" y:arg => (DescentRetainedRangeDigits.occurrences (shape.sites (y:NodeOrder.All B).1) y.2).length
local notation "reg" m:arg => rangeRegister ports r B number places.capacity places.hosts places.groups places.radix places.positive m

variable (ok : u.Ready) (small : 2*(A).candidates<2^(A).queryBits) (axes : L=R₁)
    (actorMem : Memory w) (choice : ∀i,OrdinalRead u ok small actorMem i)

def SevenOriginHeaders {U V:Type*} (origin:NodeOrder.All B→V) (tag:U→V) : Prop :=
  ∀(x:Fin (L).blocks)(j:Fin (L).operands)(f:Fin 4) h g n y,slot x n h g=some y → j.val<argc y → ∀v₀,origin y=tag v₀ →
        ((choice ((v).operandOrdinal (s) (f.castLE (by decide:4≤7)) ((j.cast (congrArg Layout.operands axes)).cast ok.slots.symm)
          (x.cast (congrArg Layout.blocks axes)) ((n.cast (congrArg Layout.nodes axes)).cast ok.nodes.symm))).amount
          (h.cast (congrArg Layout.hosts axes)) (g.cast (congrArg Layout.groups axes))).val=(ptr y j.val).header f

omit [Fintype P] in
/-- An occupied formal argument belongs to precisely the branch recorded for its node. -/
theorem registered_reset_headers {U V:Type*} (origin:NodeOrder.All B→U⊕V)
    (old : SevenOriginHeaders u r B number places shape hp pin ok small axes actorMem choice origin Sum.inl)
    (fresh : SevenOriginHeaders u r B number places shape hp pin ok small axes actorMem choice origin Sum.inr) :
    SevenHeaders u r B number places shape hp pin ok small axes actorMem choice:=by
  intro x j f h g n y hit formal
  cases found:origin y with
  | inl v₀ => exact old x j f h g n y hit formal v₀ found
  | inr v₀ => exact fresh x j f h g n y hit formal v₀ found

end
end Hierarchy.DescentSixParty.Chronology.DatePorts

end OAI
